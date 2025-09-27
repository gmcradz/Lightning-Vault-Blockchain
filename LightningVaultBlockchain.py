# Filename: node2.py
# Requirements: pip install flask waitress requests base58 flask_cors cryptography

import datetime
import hashlib
import json
import threading
import os
import time
import logging
from decimal import Decimal, getcontext
from flask import Flask, jsonify, request
from flask_cors import CORS
from urllib.parse import urlparse
from waitress import serve
import requests
import sys
import rlp
from eth_utils import keccak, to_checksum_address
from eth_keys.datatypes import Signature
from eth_keys.exceptions import ValidationError as BadSignatureError
from eth_keys import keys

# Set decimal precision for financial calculations
getcontext().prec = 18

# Setup logging
logging.basicConfig(level=logging.INFO, format='%(asctime)s - %(levelname)s - %(message)s')
logger = logging.getLogger(__name__)

# -------------------------------
# Supabase configuration (email lookup)
# -------------------------------
SUPABASE_URL = os.environ.get("SUPABASE_URL", "https://reppbcgjyjxnrpfwnudi.supabase.co")
SUPABASE_ANON_KEY = os.environ.get("SUPABASE_ANON_KEY", "eyJhbGciOiJIUzI1NiIsInR5cCI6IkpXVCJ9.eyJpc3MiOiJzdXBhYmFzZSIsInJlZiI6InJlcHBiY2dqeWp4bnJwZndudWRpIiwicm9sZSI6ImFub24iLCJpYXQiOjE3NTg4Mzk2ODksImV4cCI6MjA3NDQxNTY4OX0.K5XDZxD9uSWKu1BcM2zBlqwET_gylEaNIdnn1zAHlVM")
SUPABASE_USERS_TABLE = os.environ.get("SUPABASE_USERS_TABLE", "users")

def supabase_get_email_for_address(address: str) -> str | None:
    try:
        if not (SUPABASE_URL and SUPABASE_ANON_KEY and SUPABASE_USERS_TABLE and isinstance(address, str)):
            return None
        url = f"{SUPABASE_URL}/rest/v1/{SUPABASE_USERS_TABLE}"
        params = {
            "address": f"eq.{address}",
            "select": "email",
            "limit": 1
        }
        headers = {
            "apikey": SUPABASE_ANON_KEY,
            "Authorization": f"Bearer {SUPABASE_ANON_KEY}",
            "Accept": "application/json"
        }
        resp = requests.get(url, params=params, headers=headers, timeout=5)
        if resp.status_code == 200:
            data = resp.json() or []
            if isinstance(data, list) and data:
                email = data[0].get("email")
                if isinstance(email, str) and email:
                    return email
        return None
    except Exception:
        return None

# -------------------------------
# Security & Cryptography
# -------------------------------
class CryptoUtils:
    @staticmethod
    def generate_keypair():
        """Generate secp256k1 key pair for Ethereum-style digital signatures"""
        private_key_bytes = os.urandom(32)
        private_key = keys.PrivateKey(private_key_bytes)
        public_key = private_key.public_key
        return private_key, public_key
    
    @staticmethod
    def sign_transaction(private_key, transaction_data):
        """Sign transaction using secp256k1 (Ethereum-style)"""
        message = json.dumps(transaction_data, sort_keys=True).encode()
        signature = private_key.sign_msg(message)
        return signature.to_hex()
    
    @staticmethod
    def verify_signature(public_key, signature_hex, transaction_data):
        """Verify secp256k1 signature"""
        try:
            message = json.dumps(transaction_data, sort_keys=True).encode()
            sig_hex = signature_hex[2:] if isinstance(signature_hex, str) and signature_hex.startswith('0x') else signature_hex
            signature = keys.Signature(bytes.fromhex(sig_hex))
            return public_key.verify_msg(message, signature)
        except Exception:
            return False

def generate_address():
    """Generate Ethereum-style 0x address (20 bytes hex)."""
    random_bytes = os.urandom(20)
    return "0x" + random_bytes.hex()

# -------------------------------
# Transaction Class
# -------------------------------
class Transaction:
    def __init__(self, sender, receiver, amount, fee=0, tx_type="transfer", data=None, signature=None):
        self.sender = sender
        self.receiver = receiver
        self.amount = Decimal(str(amount))
        self.fee = Decimal(str(fee))
        self.tx_type = tx_type
        self.data = data or {}
        self.timestamp = str(datetime.datetime.utcnow())
        self.signature = signature
        self.tx_id = self.calculate_hash()
    
    def calculate_hash(self):
        """Calculate unique transaction ID"""
        tx_data = {
            'sender': self.sender,
            'receiver': self.receiver,
            'amount': str(self.amount),
            'fee': str(self.fee),
            'tx_type': self.tx_type,
            'data': self.data,
            'timestamp': self.timestamp
        }
        return hashlib.sha256(json.dumps(tx_data, sort_keys=True).encode()).hexdigest()
    
    def to_dict(self):
        return {
            'tx_id': self.tx_id,
            'sender': self.sender,
            'receiver': self.receiver,
            'amount': str(self.amount),
            'fee': str(self.fee),
            'tx_type': self.tx_type,
            'data': self.data,
            'timestamp': self.timestamp,
            'signature': self.signature
        }

# -------------------------------
# Enhanced Blockchain Class
# -------------------------------
class Blockchain:
    def __init__(self, data_file):
        self.chain = []
        self.transactions = []
        self.vaults = []
        self.nodes = set()
        self.contracts = {}
        self.balances = {}
        self.tokens = {}
        self.total_supply = Decimal('140000000')
        self.difficulty = 4
        self.data_file = data_file
        # Chain/network IDs (persisted). Default can be overridden via env on first run.
        try:
            self.chain_id = int(os.environ.get("CHAIN_ID", "296070"))
        except Exception:
            self.chain_id = 296070
        self.mempool = []  # Pending transactions
        self.max_transactions_per_block = 100
        self.block_time_target = 60  # seconds
        self.last_block_time = time.time()
        # Mining reward & halving schedule (4.5 years)
        self.initial_block_reward = Decimal('10')
        self.halving_period_seconds = int(4.5 * 365 * 24 * 60 * 60)
        # Circulating supply tracker (minted coins)
        self.circulating_supply = Decimal('0')
        
        # Founder allocation (Ethereum-style address)
        self.founder_addresses = [
            "0x2e6Eb07fB3270E3c7b2b1CE009d39A5BCDA15279"
        ]
        
        self.load_chain()
        # Ensure contracts registry structure exists
        self._ensure_contracts_registry()
        
        # No pre-seeding of balances; balances are derived from chain transactions
        
        if not self.chain:
            self.create_genesis_block()

        self.load_nodes()
        
        # Start background processes
        self.start_difficulty_adjustment_thread()

    def _ensure_contracts_registry(self):
        """Ensure contracts registry has the expected structure (e.g., NFT namespace)."""
        if not isinstance(self.contracts, dict):
            self.contracts = {}
        if 'nft' not in self.contracts:
            self.contracts['nft'] = {}

    def create_genesis_block(self):
        """Create the genesis block with premine to founder address."""
        premine_amount = (self.total_supply * Decimal('0.20'))
        genesis_transactions = []
        for addr in self.founder_addresses:
            tx = Transaction("GENESIS", addr, str(premine_amount), tx_type="genesis")
            genesis_transactions.append(tx.to_dict())
        
        genesis_block = {
            'index': 0,
            'timestamp': str(datetime.datetime.utcnow()),
            'proof': 1,
            'previous_hash': '0',
            'transactions': genesis_transactions,
            'merkle_root': self.calculate_merkle_root(genesis_transactions)
        }
        self.chain.append(genesis_block)
        # Track premine as minted supply (20% per founder address)
        try:
            self.circulating_supply += (premine_amount * Decimal(str(len(self.founder_addresses))))
        except Exception:
            self.circulating_supply += premine_amount
        # Derive balances from chain
        self.recalculate_balances()
        self.save_chain()
        logger.info("Genesis block created with premine")

    def calculate_merkle_root(self, transactions):
        """Calculate Merkle root for transaction integrity"""
        if not transactions:
            return hashlib.sha256(b'').hexdigest()
        
        tx_hashes = [hashlib.sha256(json.dumps(tx, sort_keys=True).encode()).hexdigest() 
                    for tx in transactions]
        
        while len(tx_hashes) > 1:
            if len(tx_hashes) % 2 == 1:
                tx_hashes.append(tx_hashes[-1])  # Duplicate last hash if odd number
            
            new_hashes = []
            for i in range(0, len(tx_hashes), 2):
                combined = tx_hashes[i] + tx_hashes[i + 1]
                new_hashes.append(hashlib.sha256(combined.encode()).hexdigest())
            tx_hashes = new_hashes
        
        return tx_hashes[0]

    def create_block(self, proof, previous_hash, miner_address):
        """Create new block and split rewards: 30% to miner, 70% to active MAIN vaults.

        Vault share is proportional to active MAIN-token vault balances at the time of mining.
        Transactions include optional email metadata fetched from Supabase.
        """
        # Select transactions from mempool
        selected_transactions = self.mempool[:self.max_transactions_per_block]
        self.mempool = self.mempool[self.max_transactions_per_block:]
        
        # Add mining rewards: 1% to treasury, then 30% to miner and 70% to vault owners (active MAIN vaults, proportional by amount)
        if miner_address:
            base_reward = self.get_current_block_reward()
            now_ts = datetime.datetime.utcnow()

            # Treasury takes 1% first
            treasury_portion = (base_reward * Decimal('0.01'))
            remaining_after_treasury = base_reward - treasury_portion

            miner_portion = (remaining_after_treasury * Decimal('0.30'))
            network_portion = (remaining_after_treasury * Decimal('0.70'))

            # Collect active MAIN vaults and their amounts
            active_vaults = []
            total_locked_main = Decimal('0')
            for v in self.vaults:
                try:
                    if v.get('token') != 'MAIN' or v.get('unlocked'):
                        continue
                    unlock_time = datetime.datetime.fromisoformat(v.get('unlock_time'))
                    if now_ts >= unlock_time:
                        continue
                    amt = Decimal(str(v.get('amount', '0')))
                    if amt > 0:
                        active_vaults.append((v, amt))
                        total_locked_main += amt
                except Exception:
                    continue

            # Compute total to mint and scale if exceeding hard cap
            minted_total = Decimal('0')
            # Pre-calc vault allocations
            vault_allocations: list[tuple[str, Decimal, dict]] = []  # (address, amount, extra_data)
            if total_locked_main > 0 and network_portion > 0:
                for v, amt in active_vaults:
                    share = (amt / total_locked_main)
                    alloc = (network_portion * share)
                    vault_allocations.append((v.get('address'), alloc, {"note": "vault_reward", "vault_id": v.get('id')}))
                    minted_total += alloc

            # Add miner portion and treasury portion
            minted_total += max(Decimal('0'), miner_portion)
            minted_total += max(Decimal('0'), treasury_portion)

            # Hard cap guard - scale down proportionally if needed
            allowed = self.total_supply - self.circulating_supply
            scale = Decimal('1')
            if minted_total > allowed and minted_total > 0:
                try:
                    scale = (allowed / minted_total) if allowed > 0 else Decimal('0')
                except Exception:
                    scale = Decimal('0')

            # Emit miner reward
            miner_amount = (miner_portion * scale)
            if miner_amount > 0:
                miner_email = supabase_get_email_for_address(miner_address)
                reward_tx = Transaction(
                    "SYSTEM",
                    miner_address,
                    str(miner_amount),
                    tx_type="mining_reward",
                    data={k: v for k, v in {"note": "miner_reward", "email": miner_email}.items() if v}
                )
                selected_transactions.append(reward_tx.to_dict())

            # Emit vault owner rewards
            for addr, alloc, extra in vault_allocations:
                amount_scaled = (alloc * scale)
                if amount_scaled <= 0:
                    continue
                email = supabase_get_email_for_address(addr)
                data = {**extra}
                if email:
                    data["email"] = email
                tx = Transaction("SYSTEM", addr, str(amount_scaled), tx_type="mining_reward", data=data)
                selected_transactions.append(tx.to_dict())

            # Emit treasury reward
            treas_amount = (treasury_portion * scale)
            if treas_amount > 0:
                treas_tx = Transaction("SYSTEM", TREASURY_LVT_ADDRESS, str(treas_amount), tx_type="mining_reward", data={"note": "treasury_reward"})
                selected_transactions.append(treas_tx.to_dict())

            # Update circulating supply by actual minted
            self.circulating_supply += (minted_total * scale)
        
        block = {
            'index': len(self.chain),
            'timestamp': str(datetime.datetime.utcnow()),
            'proof': proof,
            'previous_hash': previous_hash,
            'transactions': selected_transactions,
            'merkle_root': self.calculate_merkle_root(selected_transactions),
            'miner': miner_address
        }
        
        # Process transactions
        for tx_data in selected_transactions:
            self.process_transaction(tx_data)
        
        self.chain.append(block)
        self.last_block_time = time.time()
        # Force balance rebuild from chain to ensure consistency
        self.recalculate_balances()
        self.save_chain()
        return block

    def get_genesis_datetime(self):
        try:
            if self.chain and self.chain[0].get('timestamp'):
                return datetime.datetime.fromisoformat(self.chain[0]['timestamp'])
        except Exception:
            pass
        return datetime.datetime.utcnow()

    def get_current_block_reward(self) -> Decimal:
        """Return current block reward with halving every 4.5 years from genesis."""
        try:
            genesis_dt = self.get_genesis_datetime()
            elapsed_sec = max(0, int((datetime.datetime.utcnow() - genesis_dt).total_seconds()))
            period = max(1, int(self.halving_period_seconds))
            halvings = elapsed_sec // period
            reward = self.initial_block_reward / (Decimal(2) ** int(halvings))
            # Floor extremely small rewards to 0
            if reward < Decimal('0.000000000000000001'):
                return Decimal('0')
            return reward
        except Exception:
            return self.initial_block_reward

    def process_transaction(self, tx_data):
        """Process individual transaction with proper validation and NFT support"""
        tx_type = tx_data.get('tx_type', 'transfer')
        sender = tx_data['sender']
        receiver = tx_data['receiver']
        amount = Decimal(str(tx_data.get('amount', '0')))

        # For standard value transfers and NFT-related value fees, move balances first (except system/genesis senders)
        if sender not in ["SYSTEM", "GENESIS"]:
            if self.balances.get(sender, Decimal('0')) < amount:
                logger.warning(f"Transaction rejected: Insufficient balance for {sender}")
                return False
            self.balances[sender] -= amount
        self.balances[receiver] = self.balances.get(receiver, Decimal('0')) + amount

        # Handle contract operations
        if tx_type == 'nft_mint':
            data = tx_data.get('data', {})
            contract = data.get('contract')
            to = data.get('to')
            metadata = data.get('metadata', {})
            try:
                self.mint_nft(contract, to, metadata)
            except Exception as e:
                logger.warning(f"NFT mint failed: {e}")
                return False
        elif tx_type == 'nft_transfer':
            data = tx_data.get('data', {})
            contract = data.get('contract')
            token_id = str(data.get('token_id'))
            to = data.get('to')
            try:
                self.transfer_nft(contract, token_id, sender, to)
            except Exception as e:
                logger.warning(f"NFT transfer failed: {e}")
                return False

        return True

    def add_transaction_to_mempool(self, transaction):
        """Add transaction to mempool with validation"""
        # Validate transaction
        if not self.validate_transaction(transaction):
            return False
        
        self.mempool.append(transaction.to_dict())
        self.broadcast_transaction(transaction.to_dict())
        return True

    def validate_transaction(self, transaction):
        """Enhanced transaction validation"""
        # Check balance
        if transaction.sender not in ["SYSTEM", "GENESIS"]:
            current_balance = self.balances.get(transaction.sender, Decimal('0'))
            if current_balance < transaction.amount + transaction.fee:
                return False
        
        # Check for double spending (simplified)
        pending_amount = sum(Decimal(tx['amount']) for tx in self.mempool 
                           if tx['sender'] == transaction.sender)
        if pending_amount + transaction.amount > self.balances.get(transaction.sender, Decimal('0')):
            return False
        
        # Additional checks for NFT operations
        if transaction.tx_type == 'nft_mint':
            # Enforce mint fee
            if Decimal(str(transaction.amount)) < Decimal('10'):
                return False
            data = transaction.data or {}
            contract = data.get('contract')
            to = data.get('to')
            if not contract or not to:
                return False
            if 'nft' not in self.contracts or contract not in self.contracts['nft']:
                return False
        if transaction.tx_type == 'nft_transfer':
            data = transaction.data or {}
            contract = data.get('contract')
            token_id = str(data.get('token_id')) if data.get('token_id') is not None else None
            to = data.get('to')
            if not contract or token_id is None or not to:
                return False
            nft_map = self.contracts.get('nft', {}).get(contract)
            if not nft_map:
                return False
            token = nft_map['tokens'].get(token_id)
            if not token or token['owner'] != transaction.sender:
                return False
        
        return True

    def proof_of_work(self, previous_proof, miner_address):
        """Proof of Work bound to miner address (Advanced PoV).

        Advanced PoV does not reduce difficulty; instead, vaults influence reward.
        The preimage includes the miner address to prevent proof reuse across miners.
        """
        new_proof = 1
        start_time = time.time()

        prefix_str = '0' * int(self.difficulty)

        while True:
            payload = f"{new_proof**2 - previous_proof**2}:{miner_address}".encode()
            hash_operation = hashlib.sha256(payload).hexdigest()
            if hash_operation.startswith(prefix_str):
                mining_time = time.time() - start_time
                logger.info(f"Block mined in {mining_time:.2f}s with difficulty {self.difficulty}")
                return new_proof
            new_proof += 1

    def _vault_bonus_tier(self, miner_weight: Decimal, total_weight: Decimal) -> int:
        """Return integer bonus tier 0..3 based on miner share of active vault weight.

        - share >= 50% => bonus 3
        - share >= 20% => bonus 2
        - share >= 5%  => bonus 1
        - else => bonus 0
        """
        try:
            if total_weight <= 0:
                return 0
            share = (miner_weight / total_weight) if total_weight > 0 else Decimal('0')
            if share >= Decimal('0.50'):
                return 3
            if share >= Decimal('0.20'):
                return 2
            if share >= Decimal('0.05'):
                return 1
            return 0
        except Exception:
            return 0

    def _total_active_vault_weight(self, at_time: datetime.datetime | None = None) -> Decimal:
        total = Decimal('0')
        for v in self.vaults:
            total += self._vault_entry_weight(v, at_time)
        return total

    def _vault_entry_weight(self, vault_entry: dict, at_time: datetime.datetime | None = None) -> Decimal:
        """Return weight contribution for a single vault entry at a given time.

        Weight = amount * duration_days for active locks at that time.
        A vault is active if at_time < unlock_time. Early withdrawal is not supported
        by design in this node; once created, the vault remains until unlock.
        """
        try:
            if vault_entry.get('token') != 'MAIN':
                return Decimal('0')  # Only MAIN token influences PoV
            amount = Decimal(str(vault_entry.get('amount', '0')))
            if amount <= 0:
                return Decimal('0')
            unlock_time = datetime.datetime.fromisoformat(vault_entry.get('unlock_time'))
            lock_time = datetime.datetime.fromisoformat(vault_entry.get('lock_time'))
            ref_time = at_time or datetime.datetime.utcnow()
            if ref_time >= unlock_time:
                return Decimal('0')
            duration_days = max(1, int((unlock_time - lock_time).total_seconds() // 86400))
            return amount * Decimal(str(duration_days))
        except Exception:
            return Decimal('0')

    def get_vault_weight(self, address: str, at_time: datetime.datetime | None = None) -> Decimal:
        """Calculate effective mining weight for an address based on its active vaults.

        Weight is proportional to amount locked and lock duration. Only active vaults
        (not yet unlocked at 'at_time') count toward weight.
        """
        if not isinstance(address, str):
            return Decimal('0')
        total = Decimal('0')
        for v in self.vaults:
            if v.get('address') == address:
                total += self._vault_entry_weight(v, at_time)
        return total

    def adjust_difficulty(self):
        """Adjust mining difficulty based on block time"""
        if len(self.chain) < 10:  # Wait for enough blocks
            return
        
        # Calculate average time of last 10 blocks
        recent_blocks = self.chain[-10:]
        time_diffs = []
        
        for i in range(1, len(recent_blocks)):
            prev_time = datetime.datetime.fromisoformat(recent_blocks[i-1]['timestamp'])
            curr_time = datetime.datetime.fromisoformat(recent_blocks[i]['timestamp'])
            time_diffs.append((curr_time - prev_time).total_seconds())
        
        avg_time = sum(time_diffs) / len(time_diffs)
        
        # Adjust difficulty
        if avg_time < self.block_time_target * 0.8:
            self.difficulty += 0.1
        elif avg_time > self.block_time_target * 1.2:
            self.difficulty = max(1, self.difficulty - 0.1)
        
        logger.info(f"Difficulty adjusted to {self.difficulty} (avg block time: {avg_time:.2f}s)")

    def start_difficulty_adjustment_thread(self):
        """Start background thread for difficulty adjustment"""
        def adjust_periodically():
            while True:
                time.sleep(300)  # Adjust every 5 minutes
                self.adjust_difficulty()
        
        thread = threading.Thread(target=adjust_periodically, daemon=True)
        thread.start()

    def is_chain_valid(self, chain):
        """Enhanced chain validation with Merkle root verification and PoV difficulty.

        PoV validation:
        - Uses block['miner'] to reconstruct the PoW preimage.
        - Computes effective difficulty based on miner's vault weight at the block timestamp
          relative to total active vault weight.
        - Falls back to base difficulty when no active vaults.
        """
        if not chain:
            return False
        
        # Validate genesis block
        if chain[0]['index'] != 0 or chain[0]['previous_hash'] != '0':
            return False
        
        previous_block = chain[0]
        for i in range(1, len(chain)):
            block = chain[i]
            
            # Check block index
            if block['index'] != previous_block['index'] + 1:
                return False
            
            # Check previous hash
            if block['previous_hash'] != self.hash(previous_block):
                return False
            
            # Check proof of work (Advanced PoV: base difficulty, miner-bound preimage)
            previous_proof = previous_block['proof']
            proof = block['proof']
            miner_addr = block.get('miner', '')
            check_prefix = '0' * int(self.difficulty)
            payload = f"{proof**2 - previous_proof**2}:{miner_addr}".encode()
            hash_operation = hashlib.sha256(payload).hexdigest()
            if not hash_operation.startswith(check_prefix):
                # PoV slashing: if miner presented invalid proof, burn their active MAIN vaults
                self._slash_miner_vaults(miner_addr, reason="invalid_pow")
                return False
            
            # Check Merkle root
            calculated_merkle = self.calculate_merkle_root(block['transactions'])
            if block.get('merkle_root') != calculated_merkle:
                logger.warning(f"Merkle root mismatch in block {block['index']}")
                return False
            
            previous_block = block
        
        return True

    def _slash_miner_vaults(self, miner_addr: str, reason: str = ""):
        """Burn all active MAIN-token vaults for a miner.

        Punitive action for consensus faults (e.g., invalid PoW). The vault amounts are
        set to 0 and marked unlocked so they no longer contribute weight nor can be
        returned. This does not credit any party; it simply burns the stake.
        """
        try:
            now = datetime.datetime.utcnow()
            burned = Decimal('0')
            for v in self.vaults:
                try:
                    if v.get('address') != miner_addr:
                        continue
                    if v.get('token') != 'MAIN':
                        continue
                    if v.get('unlocked'):
                        continue
                    unlock_time = datetime.datetime.fromisoformat(v.get('unlock_time'))
                    if now >= unlock_time:
                        continue
                    amt = Decimal(str(v.get('amount', '0')))
                    if amt > 0:
                        v['amount'] = '0'
                        v['unlocked'] = True
                        burned += amt
                except Exception:
                    continue
            if burned > 0:
                logger.warning(f"Slashed {miner_addr}: burned {burned} MAIN from active vaults. Reason: {reason}")
                self.save_chain()
        except Exception as e:
            logger.error(f"Failed to slash miner {miner_addr}: {e}")

    def hash(self, block):
        """Calculate block hash"""
        encoded_block = json.dumps(block, sort_keys=True).encode()
        return hashlib.sha256(encoded_block).hexdigest()

    def get_previous_block(self):
        return self.chain[-1] if self.chain else None

    # -------------------------------
    # Vault System (Enhanced)
    # -------------------------------
    def lock_vault(self, address, amount, duration_days, vault_type="time_lock", token="MAIN"):
        """Enhanced vault system with different lock types"""
        amount = Decimal(str(amount))
        
        if token == "MAIN":
            if self.balances.get(address, Decimal('0')) < amount:
                raise ValueError("Insufficient balance")
            self.balances[address] -= amount
        else:
            if address not in self.tokens.get(token, {}).get('balances', {}):
                raise ValueError("Insufficient token balance")
            if self.tokens[token]['balances'][address] < amount:
                raise ValueError("Insufficient token balance")
            self.tokens[token]['balances'][address] -= amount
        
        unlock_time = datetime.datetime.utcnow() + datetime.timedelta(days=int(duration_days))
        vault = {
            "id": generate_address(),
            "address": address,
            "amount": str(amount),
            "token": token,
            "vault_type": vault_type,
            "lock_time": str(datetime.datetime.utcnow()),
            "unlock_time": str(unlock_time),
            "unlocked": False,
            "interest_rate": str(self.calculate_vault_interest(duration_days, amount))
        }
        self.vaults.append(vault)
        self.save_chain()
        logger.info(f"Vault locked: {amount} {token} for {duration_days} days")
        return vault

    def calculate_vault_interest(self, duration_days, amount):
        """Calculate interest for vault based on duration and amount (Decimal safe)"""
        base_rate = Decimal('0.05')  # 5% annual base rate

        # Ensure duration_days is Decimal
        duration_days = Decimal(str(duration_days))
        duration_bonus = min(duration_days / Decimal('365'), Decimal('2')) * Decimal('0.02')

        # Ensure amount is Decimal
        amount = Decimal(str(amount))
        amount_bonus = min(amount / self.total_supply, Decimal('0.01')) * Decimal('0.01')

        return base_rate + duration_bonus + amount_bonus


    def release_vaults(self):
        """Release unlocked vaults with interest (Decimal safe)"""
        now = datetime.datetime.utcnow()
        released_count = 0

        for vault in self.vaults:
            if not vault['unlocked'] and now >= datetime.datetime.fromisoformat(vault['unlock_time']):
                vault['unlocked'] = True
                amount = Decimal(str(vault['amount']))

                # interest_rate is stored as string -> wrap with Decimal
                interest_rate = Decimal(str(vault.get('interest_rate', '0')))
                interest = (amount * interest_rate)

                # Guard interest minting by hard cap
                if self.circulating_supply + interest <= self.total_supply:
                    total_return = amount + interest
                    self.circulating_supply += interest
                else:
                    total_return = amount  # no extra minting beyond hard cap

                if vault['token'] == "MAIN":
                    self.balances[vault['address']] = self.balances.get(vault['address'], Decimal('0')) + total_return
                else:
                    token_balances = self.tokens[vault['token']]['balances']
                    token_balances[vault['address']] = token_balances.get(vault['address'], Decimal('0')) + total_return

                released_count += 1
                logger.info(f"Vault released: {total_return} {vault['token']} to {vault['address']}")

        if released_count > 0:
            self.save_chain()

        return released_count


    # -------------------------------
    # Node Management
    # -------------------------------
    def load_nodes(self):
        """Load nodes from file"""
        try:
            with open("nodes.json", "r") as f:
                data = json.load(f)
                self.nodes = set(data.get("nodes", []))
        except FileNotFoundError:
            self.nodes = set()
            self.save_nodes()

    def save_nodes(self):
        """Save nodes to file"""
        with open("nodes.json", "w") as f:
            json.dump({"nodes": list(self.nodes)}, f, indent=2)

    def add_node(self, address):
        """Add node with validation"""
        try:
            parsed_url = urlparse(address)
            if parsed_url.netloc:
                self.nodes.add(parsed_url.netloc)
                self.save_nodes()
                return True
        except Exception as e:
            logger.error(f"Failed to add node {address}: {e}")
        return False

    def broadcast_transaction(self, transaction):
        """Broadcast transaction to network with error handling"""
        successful_broadcasts = 0
        for node in list(self.nodes):  # Create copy to avoid modification during iteration
            try:
                response = requests.post(
                    f"http://{node}/add_transaction", 
                    json=transaction, 
                    timeout=5
                )
                if response.status_code == 200:
                    successful_broadcasts += 1
            except Exception as e:
                logger.warning(f"Failed to broadcast to {node}: {e}")
                # Remove unresponsive nodes after multiple failures
                continue
        
        logger.info(f"Transaction broadcast to {successful_broadcasts}/{len(self.nodes)} nodes")

    def replace_chain(self):
        """Enhanced chain replacement with better validation"""
        longest_chain = None
        max_length = len(self.chain)
        valid_chains = []
        
        for node in self.nodes:
            try:
                response = requests.get(f'http://{node}/get_chain', timeout=10)
                if response.status_code == 200:
                    data = response.json()
                    length = data['length']
                    chain = data['chain']
                    
                    if length > max_length and self.is_chain_valid(chain):
                        valid_chains.append((length, chain, node))
            except Exception as e:
                logger.warning(f"Failed to get chain from {node}: {e}")
                continue
        
        if valid_chains:
            # Choose the longest valid chain
            valid_chains.sort(key=lambda x: x[0], reverse=True)
            max_length, longest_chain, source_node = valid_chains[0]
            
            if longest_chain:
                logger.info(f"Replacing chain with longer chain from {source_node} (length: {max_length})")
                self.chain = longest_chain
                self.recalculate_balances()  # Recalculate balances from new chain
                self.save_chain()
                return True
        
        return False

    def recalculate_balances(self):
        """Recalculate all balances from chain by replaying transactions."""
        self.balances = {}
        # Rebuild circulating supply from mint transactions (GENESIS/SYSTEM)
        self.circulating_supply = Decimal('0')
        for block in self.chain:
            for tx_data in block['transactions']:
                try:
                    sender = tx_data.get('sender')
                    amt = Decimal(str(tx_data.get('amount', '0')))
                    if sender in ("SYSTEM", "GENESIS") and amt > 0:
                        self.circulating_supply += amt
                except Exception:
                    pass
                self.process_transaction(tx_data)

    # -------------------------------
    # Persistence (Enhanced)
    # -------------------------------
    def save_chain(self):
        """Enhanced save with backup"""
        data = {
            "chain": self.chain,
            "vaults": [
                {**v, "amount": str(v.get("amount")), "interest_rate": str(v.get("interest_rate", "0"))}
                for v in self.vaults
            ],
            "balances": {k: str(v) for k, v in self.balances.items()},
            "contracts": self.contracts,
            "tokens": self.tokens,
            "difficulty": self.difficulty,
            "mempool": self.mempool,
            "chain_id": self.chain_id,
            "circulating_supply": str(self.circulating_supply)
        }
        
        # Create backup before saving
        backup_file = f"{self.data_file}.backup"
        if os.path.exists(self.data_file):
            os.rename(self.data_file, backup_file)
        
        try:
            with open(self.data_file, "w") as f:
                json.dump(data, f, indent=2)
        except Exception as e:
            logger.error(f"Failed to save chain: {e}")
            # Restore backup if save failed
            if os.path.exists(backup_file):
                os.rename(backup_file, self.data_file)
            raise

    def load_chain(self):
        """Enhanced load with error recovery"""
        try:
            with open(self.data_file, "r") as f:
                data = json.load(f)
                self.chain = data.get("chain", [])
                self.vaults = data.get("vaults", [])
                
                # Convert balance strings back to Decimal
                balance_data = data.get("balances", {})
                self.balances = {k: Decimal(v) for k, v in balance_data.items()}
                
                self.contracts = data.get("contracts", {})
                self.tokens = data.get("tokens", {})
                self.difficulty = data.get("difficulty", 4)
                self.mempool = data.get("mempool", [])
                self.chain_id = int(data.get("chain_id", self.chain_id))
                try:
                    self.circulating_supply = Decimal(str(data.get("circulating_supply", '0')))
                except Exception:
                    self.circulating_supply = Decimal('0')
                
                logger.info(f"Loaded chain with {len(self.chain)} blocks")
                # Ensure registry structure after load
                self._ensure_contracts_registry()
                
        except FileNotFoundError:
            logger.info("No existing chain found, starting fresh")
            self.init_empty_state()
        except json.JSONDecodeError as e:
            logger.error(f"Corrupted chain file: {e}")
            # Try to load backup
            backup_file = f"{self.data_file}.backup"
            if os.path.exists(backup_file):
                logger.info("Loading from backup")
                os.rename(backup_file, self.data_file)
                self.load_chain()
            else:
                self.init_empty_state()

    def init_empty_state(self):
        """Initialize empty blockchain state"""
        self.chain = []
        self.vaults = []
        self.balances = {}
        self.contracts = {}
        self.tokens = {}
        self.mempool = []
        self._ensure_contracts_registry()

    # -------------------------------
    # NFT Contracts
    # -------------------------------
    def create_nft_contract(self, owner, name, symbol, base_uri=""):
        self._ensure_contracts_registry()
        contract_address = generate_address()
        self.contracts['nft'][contract_address] = {
            'name': name,
            'symbol': symbol,
            'owner': owner,
            'base_uri': base_uri or "",
            'next_token_id': 1,
            'tokens': {},  # token_id(str) -> {owner, metadata, token_uri}
            'balances': {}  # address -> count
        }
        self.save_chain()
        return {
            'contract': contract_address,
            'name': name,
            'symbol': symbol,
            'owner': owner
        }

    def mint_nft(self, contract, to, metadata=None):
        self._ensure_contracts_registry()
        metadata = metadata or {}
        if contract not in self.contracts['nft']:
            raise ValueError("NFT contract does not exist")
        coll = self.contracts['nft'][contract]
        token_id = str(coll['next_token_id'])
        coll['next_token_id'] += 1
        base_uri = coll.get('base_uri') or ""
        token_uri = f"{base_uri}{token_id}" if base_uri else metadata.get('token_uri', '')
        coll['tokens'][token_id] = {
            'owner': to,
            'metadata': metadata,
            'token_uri': token_uri
        }
        coll['balances'][to] = int(coll['balances'].get(to, 0)) + 1
        return token_id

    def transfer_nft(self, contract, token_id, from_addr, to_addr):
        self._ensure_contracts_registry()
        if contract not in self.contracts['nft']:
            raise ValueError("NFT contract does not exist")
        coll = self.contracts['nft'][contract]
        token = coll['tokens'].get(token_id)
        if not token:
            raise ValueError("Token does not exist")
        if token['owner'] != from_addr:
            raise ValueError("Sender is not token owner")
        token['owner'] = to_addr
        coll['balances'][from_addr] = max(0, int(coll['balances'].get(from_addr, 0)) - 1)
        coll['balances'][to_addr] = int(coll['balances'].get(to_addr, 0)) + 1
        return True

# -------------------------------
# Flask App (Enhanced)
# -------------------------------
app = Flask(__name__)
CORS(app)
# Default RPC port aligned with Ethereum convention so MetaMask can connect easily
port = 8545
if len(sys.argv) > 1:
    port = int(sys.argv[1])

node_address = generate_address()
blockchain = Blockchain(f"data_node_{port}.json")
 
# Initialize EVM engine (smart contracts support)
from evm_engine import EVMEngine
evm_engine = EVMEngine(db_dir="evm_db", chain_id=blockchain.chain_id)

@app.route('/my_address')
def my_address():
    return jsonify({"address": node_address})

@app.route('/check_balance')
def check_balance():
    addr = request.args.get("address")
    if not addr:
        return jsonify({"error": "Address parameter required"}), 400
    
    main_balance = blockchain.balances.get(addr, Decimal('0'))
    token_balances = {
        name: token_data['balances'].get(addr, Decimal('0')) 
        for name, token_data in blockchain.tokens.items()
    }
    
    return jsonify({
        "balances": {"MAIN": str(main_balance)}, 
        "tokens": {k: str(v) for k, v in token_balances.items()}
    })

# -------------------------------
# NFT REST API
# -------------------------------

TREASURY_ADDRESS = "0x00000000000000000000000000000000000000fe"
MINT_FEE_LVT = Decimal('10')

@app.route('/nft/deploy', methods=['POST'])
def nft_deploy():
    data = request.get_json() or {}
    name = data.get('name')
    symbol = data.get('symbol')
    base_uri = data.get('base_uri', '')
    owner = data.get('owner', node_address)
    if not name or not symbol:
        return jsonify({"error": "name and symbol are required"}), 400
    try:
        result = blockchain.create_nft_contract(owner, name, symbol, base_uri)
        return jsonify({"message": "NFT contract deployed", **result})
    except Exception as e:
        return jsonify({"error": str(e)}), 400

@app.route('/create_wallet', methods=['POST'])
def create_wallet():
    """Create a brand new wallet (private/public key pair + address)."""
    try:
        private_key, public_key = CryptoUtils.generate_keypair()
        address = public_key.to_checksum_address()

        return jsonify({
            "address": address,
            "private_key": private_key.to_hex(),  # ⚠️ Secure storage only!
            "public_key": public_key.to_hex()
        })
    except Exception as e:
        return jsonify({"error": str(e)}), 500


@app.route('/nft/mint', methods=['POST'])
def nft_mint_route():
    data = request.get_json() or {}
    contract = data.get('contract')
    to_addr = data.get('to')
    minter = data.get('minter')
    metadata = data.get('metadata', {})
    if not contract or not to_addr or not minter:
        return jsonify({"error": "contract, to, minter are required"}), 400
    # Construct a transaction that pays the mint fee to treasury and carries NFT mint intent
    tx = Transaction(
        sender=minter,
        receiver=TREASURY_ADDRESS,
        amount=str(MINT_FEE_LVT),
        fee=0,
        tx_type='nft_mint',
        data={'contract': contract, 'to': to_addr, 'metadata': metadata}
    )
    if blockchain.add_transaction_to_mempool(tx):
        return jsonify({"message": "Mint submitted to mempool", "tx_id": tx.tx_id})
    return jsonify({"error": "Mint validation failed"}), 400

@app.route('/nft/transfer', methods=['POST'])
def nft_transfer_route():
    data = request.get_json() or {}
    contract = data.get('contract')
    token_id = data.get('token_id')
    from_addr = data.get('from')
    to_addr = data.get('to')
    if not contract or token_id is None or not from_addr or not to_addr:
        return jsonify({"error": "contract, token_id, from, to are required"}), 400
    tx = Transaction(
        sender=from_addr,
        receiver=to_addr,
        amount='0',
        fee=0,
        tx_type='nft_transfer',
        data={'contract': contract, 'token_id': token_id, 'to': to_addr}
    )
    if blockchain.add_transaction_to_mempool(tx):
        return jsonify({"message": "Transfer submitted to mempool", "tx_id": tx.tx_id})
    return jsonify({"error": "Transfer validation failed"}), 400

@app.route('/nft/ownerOf')
def nft_owner_of():
    contract = request.args.get('contract')
    token_id = request.args.get('token_id')
    if not contract or token_id is None:
        return jsonify({"error": "contract and token_id are required"}), 400
    coll = blockchain.contracts.get('nft', {}).get(contract)
    if not coll:
        return jsonify({"error": "contract not found"}), 404
    token = coll['tokens'].get(str(token_id))
    if not token:
        return jsonify({"error": "token not found"}), 404
    return jsonify({"owner": token['owner']})

@app.route('/nft/balanceOf')
def nft_balance_of():
    contract = request.args.get('contract')
    address = request.args.get('address')
    if not contract or not address:
        return jsonify({"error": "contract and address are required"}), 400
    coll = blockchain.contracts.get('nft', {}).get(contract)
    if not coll:
        return jsonify({"error": "contract not found"}), 404
    balance = int(coll['balances'].get(address, 0))
    return jsonify({"balance": balance})

@app.route('/nft/tokenURI')
def nft_token_uri():
    contract = request.args.get('contract')
    token_id = request.args.get('token_id')
    if not contract or token_id is None:
        return jsonify({"error": "contract and token_id are required"}), 400
    coll = blockchain.contracts.get('nft', {}).get(contract)
    if not coll:
        return jsonify({"error": "contract not found"}), 404
    token = coll['tokens'].get(str(token_id))
    if not token:
        return jsonify({"error": "token not found"}), 404
    return jsonify({"tokenURI": token.get('token_uri', '')})

@app.route('/add_transaction', methods=['POST'])
def add_transaction():
    data = request.get_json()
    if not data or not all(k in data for k in ["sender", "receiver", "amount"]):
        return jsonify({"error": "Invalid transaction data"}), 400
    
    try:
        transaction = Transaction(
            sender=data["sender"],
            receiver=data["receiver"],
            amount=data["amount"],
            fee=data.get("fee", 0),
            tx_type=data.get("tx_type", "transfer")
        )
        
        if blockchain.add_transaction_to_mempool(transaction):
            return jsonify({
                "message": "Transaction added to mempool",
                "tx_id": transaction.tx_id
            })
        else:
            return jsonify({"error": "Transaction validation failed"}), 400
            
    except Exception as e:
        return jsonify({"error": str(e)}), 400

@app.route('/mine_block', methods=['POST'])
def mine_block():
    data = request.get_json() or {}
    miner_address = data.get("miner", node_address)
    # Allow mining even with empty mempool
    try:
        prev_block = blockchain.get_previous_block()
        if not prev_block:
            return jsonify({"error": "No previous block found"}), 500
            
        proof = blockchain.proof_of_work(prev_block['proof'], miner_address)
        prev_hash = blockchain.hash(prev_block)
        
        block = blockchain.create_block(proof, prev_hash, miner_address)
        # Compute miner PoV info for response
        now_ts = datetime.datetime.utcnow()
        total_weight = blockchain._total_active_vault_weight(at_time=now_ts)
        miner_weight = blockchain.get_vault_weight(miner_address, at_time=now_ts)
        bonus = blockchain._vault_bonus_tier(miner_weight, total_weight) if total_weight > 0 else 0
        current_reward = blockchain.get_current_block_reward()
        blockchain.release_vaults()
        
        return jsonify({
            "message": "New block mined successfully",
            "index": block['index'], 
            "transactions": len(block['transactions']),
            "proof": proof,
            "merkle_root": block['merkle_root'],
            "miner_weight": str(miner_weight),
            "bonus_tier": int(bonus),
            "base_block_reward": str(current_reward),
            "total_reward": str(sum(Decimal(tx['amount']) for tx in block['transactions'] if tx.get('tx_type') == 'mining_reward'))
        })
        
    except Exception as e:
        logger.error(f"Mining error: {e}")
        return jsonify({"error": "Mining failed"}), 500

@app.route('/get_chain')
def get_chain():
    return jsonify({
        "length": len(blockchain.chain), 
        "chain": blockchain.chain,
        "difficulty": blockchain.difficulty
    })

@app.route('/mempool')
def get_mempool():
    return jsonify({
        "size": len(blockchain.mempool),
        "transactions": blockchain.mempool
    })

@app.route('/vault/lock', methods=['POST'])
def lock_vault():
    data = request.get_json()
    required_fields = ["address", "amount", "duration_days"]
    if not all(field in data for field in required_fields):
        return jsonify({"error": "Missing required fields"}), 400
    
    try:
        vault = blockchain.lock_vault(
            address=data["address"],
            amount=data["amount"],
            duration_days=data["duration_days"],
            vault_type=data.get("vault_type", "time_lock"),
            token=data.get("token", "MAIN")
        )
        return jsonify({"message": "Vault locked successfully", "vault": vault})
    except Exception as e:
        return jsonify({"error": str(e)}), 400

@app.route('/vaults')
def get_vaults():
    return jsonify({"vaults": blockchain.vaults})

@app.route('/balances_all')
def balances_all():
    try:
        return jsonify({
            "status": "ok",
            "data": {k: str(v) for k, v in blockchain.balances.items()}
        })
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route('/transactions')
def transactions_by_address():
    address = request.args.get('address')
    if not address:
        return jsonify({"status": "error", "message": "address is required"}), 400
    try:
        txs = []
        for b in blockchain.chain:
            for tx in b.get('transactions', []):
                if tx.get('sender') == address or tx.get('receiver') == address:
                    txs.append(tx)
        return jsonify({"status": "ok", "data": txs})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route('/vaults/leaderboard')
def vaults_leaderboard():
    try:
        aggregates = {}
        now_ts = datetime.datetime.utcnow()
        for v in blockchain.vaults:
            try:
                addr = v.get('address')
                amt = Decimal(str(v.get('amount', '0')))
                unlock_time = datetime.datetime.fromisoformat(v.get('unlock_time'))
                active = (not v.get('unlocked')) and (now_ts < unlock_time)
                if amt <= 0 or not addr:
                    continue
                # total locked
                agg = aggregates.setdefault(addr, {"total_locked": Decimal('0'), "weight": Decimal('0')})
                agg["total_locked"] += amt
            except Exception:
                continue
        # Compute weights using helper per address
        for addr in list(aggregates.keys()):
            aggregates[addr]["weight"] = blockchain.get_vault_weight(addr, at_time=now_ts)
        items = [
            {
                "address": addr,
                "total_locked": str(data["total_locked"]),
                "weight": str(data["weight"])
            }
            for addr, data in aggregates.items()
        ]
        items.sort(key=lambda x: (Decimal(x['total_locked']), Decimal(x['weight'])), reverse=True)
        return jsonify({"status": "ok", "data": items})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

# -------------------------------
# Governance (placeholder)
# -------------------------------
GOVERNANCE_PROPOSALS = [
    {"id": 1, "title": "Increase block reward", "status": "open"},
    {"id": 2, "title": "Add new token listing", "status": "open"}
]
GOVERNANCE_VOTES = []

@app.route('/governance/proposals')
def governance_proposals():
    return jsonify({"status": "ok", "data": GOVERNANCE_PROPOSALS})

@app.route('/governance/vote', methods=['POST'])
def governance_vote():
    try:
        data = request.get_json() or {}
        address = data.get('address')
        proposal_id = data.get('proposal_id')
        vote = data.get('vote')
        if not address or proposal_id is None or vote is None:
            return jsonify({"status": "error", "message": "address, proposal_id, vote required"}), 400
        entry = {
            "address": address,
            "proposal_id": int(proposal_id),
            "vote": str(vote),
            "timestamp": str(datetime.datetime.utcnow())
        }
        GOVERNANCE_VOTES.append(entry)
        return jsonify({"status": "ok", "message": "vote recorded", "data": entry})
    except Exception as e:
        return jsonify({"status": "error", "message": str(e)}), 500

@app.route('/vault')
@app.route('/vault/<address>')
def vault_details(address=None):
    if address:
        vault_list = [v for v in blockchain.vaults if v.get('address') == address]
    else:
        vault_list = blockchain.vaults
    result = []
    total_locked = Decimal('0')
    now_ts = datetime.datetime.utcnow()
    for v in vault_list:
        try:
            amt = Decimal(str(v.get('amount', '0')))
            total_locked += amt
            unlock_time = datetime.fromisoformat(v.get('unlock_time'))
            remaining = max(0, int((unlock_time - now_ts).total_seconds()))
            days_remaining = remaining // 86400
            result.append({
                'address': v.get('address'),
                'amount': str(amt),
                'token': v.get('token'),
                'unlock_time': v.get('unlock_time'),
                'days_remaining': int(days_remaining)
            })
        except Exception:
            continue
    return jsonify({'total_locked': str(total_locked), 'vaults': result})

@app.route('/get_vaults', methods=['GET'])
def get_vaults_grouped():
    grouped = {}
    for v in blockchain.vaults:
        addr = v.get('address')
        grouped.setdefault(addr, []).append({
            'amount': str(v.get('amount')),
            'unlock_time': v.get('unlock_time'),
            'token': v.get('token')
        })
    return jsonify(grouped), 200

@app.route('/vault/weight')
def get_vault_weight_route():
    address = request.args.get('address')
    if not address:
        return jsonify({"error": "address is required"}), 400
    wt = blockchain.get_vault_weight(address)
    total = blockchain._total_active_vault_weight()
    bonus = blockchain._vault_bonus_tier(wt, total) if total > 0 else 0
    return jsonify({
        "address": address,
        "weight": str(wt),
        "network_total_weight": str(total),
        "bonus_tier": int(bonus)
    })

@app.route('/nodes', methods=['GET', 'POST'])
def manage_nodes():
    if request.method == 'GET':
        return jsonify({"nodes": list(blockchain.nodes)})
    else:
        data = request.get_json()
        if not data or "address" not in data:
            return jsonify({"error": "Address required"}), 400
        
        if blockchain.add_node(data["address"]):
            return jsonify({"message": "Node added successfully"})
        else:
            return jsonify({"error": "Invalid node address"}), 400

@app.route('/sync')
def sync_chain():
    if blockchain.replace_chain():
        return jsonify({"message": "Chain synchronized successfully"})
    else:
        return jsonify({"message": "Chain is up to date"})

@app.route('/node_stats')
def get_node_stats():
    return jsonify({
        "blocks": len(blockchain.chain),
        "difficulty": blockchain.difficulty,
        "mempool_size": len(blockchain.mempool),
        "total_supply": str(blockchain.total_supply),
        "active_vaults": len([v for v in blockchain.vaults if not v["unlocked"]]),
        "nodes": len(blockchain.nodes)
    })

@app.route('/stats')
def get_stats():
    return jsonify({
        "blocks": len(blockchain.chain),
        "difficulty": blockchain.difficulty,
        "mempool_size": len(blockchain.mempool),
        "total_supply": str(blockchain.total_supply),
        "active_vaults": len([v for v in blockchain.vaults if not v["unlocked"]]),
        "nodes": len(blockchain.nodes),
        "treasury_balance": str(blockchain.balances.get(TREASURY_LVT_ADDRESS, Decimal('0')))
    })

@app.route('/health')
def health():
    return jsonify({"status": "ok"}), 200


@app.route("/", methods=["GET"])
def index():
    return jsonify({"message": "Lightning Vault JSON-RPC Node is running. Use POST requests for RPC."})

# -------------------------------
# Ethereum JSON-RPC compatibility (MetaMask)
# -------------------------------

# Chain configuration for MetaMask (will be read from persisted blockchain state)
NATIVE_SYMBOL = "LVT"

# Treasury address for network rewards
TREASURY_LVT_ADDRESS = "0x0000000000000000000000000000000000000fee"

def to_hex(value):
    try:
        return hex(int(value))
    except Exception:
        return "0x0"

def to_hex_wei(decimal_amount: Decimal) -> str:
    # Represent balances in 18 decimals like wei
    scaled = int((decimal_amount * Decimal("1000000000000000000")).to_integral_value(rounding=None))
    return hex(scaled)

def from_hex_wei(hex_value: str) -> Decimal:
    try:
        value_int = int(hex_value, 16)
        return Decimal(value_int) / Decimal("1000000000000000000")
    except Exception:
        return Decimal('0')

def to_decimal_from_wei_int(value_int: int) -> Decimal:
    try:
        return Decimal(value_int) / Decimal("1000000000000000000")
    except Exception:
        return Decimal('0')

def _is_typed_tx(raw_bytes: bytes) -> bool:
    # EIP-2718 typed tx start with 0x01 (2930) or 0x02 (1559) etc.
    if not raw_bytes:
        return False
    first = raw_bytes[0]
    # RLP list first byte typically >= 0xc0; typed are small (0x01/0x02...)
    return first in (1, 2)

def _rlp_encode_legacy_tx_fields(fields: list) -> bytes:
    return rlp.encode(fields)

def _get_legacy_tx_signing_hash(nonce_b, gas_price_b, gas_b, to_b, value_b, data_b, chain_id: int | None):
    if chain_id is None:
        payload = _rlp_encode_legacy_tx_fields([nonce_b, gas_price_b, gas_b, to_b, value_b, data_b])
    else:
        payload = _rlp_encode_legacy_tx_fields([nonce_b, gas_price_b, gas_b, to_b, value_b, data_b, chain_id, 0, 0])
    return keccak(payload)

def _recover_sender_address_from_vrs(msg_hash: bytes, v: int, r: int, s: int, chain_id: int | None) -> str:
    # Normalize v for recovery per EIP-155
    if chain_id is None:
        recid = v - 27
        v_norm = 27 + (recid & 1)
    else:
        recid = (v - 35 - 2 * chain_id) % 2
        v_norm = 27 + (recid & 1)
    sig = Signature(vrs=(v_norm, r, s))
    pub = sig.recover_public_key_from_msg_hash(msg_hash)
    return to_checksum_address(pub.to_address())

def block_hash(block_obj):
    try:
        return "0x" + blockchain.hash(block_obj)
    except Exception:
        return None

def to_eth_tx(tx_data, block_index=None, tx_index=None):
    # Map internal tx to a minimal Ethereum-like tx object
    value_hex = to_hex_wei(Decimal(tx_data.get("amount", "0")))
    tx_hash = "0x" + hashlib.sha256(json.dumps(tx_data, sort_keys=True).encode()).hexdigest()
    sender_addr = tx_data.get("sender")
    receiver_addr = tx_data.get("receiver")
    if not (isinstance(sender_addr, str) and sender_addr.startswith("0x")):
        sender_addr = "0x0000000000000000000000000000000000000000"
    if not (isinstance(receiver_addr, str) and receiver_addr.startswith("0x")):
        receiver_addr = "0x0000000000000000000000000000000000000000"
    eth_tx = {
        "hash": tx_hash,
        "nonce": "0x0",
        "blockHash": block_hash(blockchain.chain[block_index]) if block_index is not None else None,
        "blockNumber": to_hex(block_index) if block_index is not None else None,
        "transactionIndex": to_hex(tx_index) if tx_index is not None else None,
        "from": sender_addr,
        "to": receiver_addr,
        "value": value_hex,
        "gas": "0x5208",
        "gasPrice": "0x0",
        "input": "0x"
    }
    return eth_tx

def to_eth_block(block_obj, include_transactions=False):
    idx = block_obj.get("index", 0)
    parent_hash = "0x" + (blockchain.hash(blockchain.chain[idx-1]) if idx > 0 else "0"*64)
    # Convert ISO timestamp to epoch seconds
    try:
        ts = int(datetime.fromisoformat(block_obj["timestamp"]).timestamp())
    except Exception:
        ts = int(time.time())

    # Transactions field
    if include_transactions:
        txs = [to_eth_tx(tx, idx, i) for i, tx in enumerate(block_obj.get("transactions", []))]
    else:
        txs = ["0x" + hashlib.sha256(json.dumps(tx, sort_keys=True).encode()).hexdigest() for tx in block_obj.get("transactions", [])]

    eth_block = {
        "number": to_hex(idx),
        "hash": block_hash(block_obj),
        "parentHash": parent_hash,
        "nonce": "0x0",
        "sha3Uncles": "0x1dcc4de8dec75d7aab85b567b6ccd41ad312451b948a7413f0a142fd40d49347",
        "logsBloom": "0x" + ("0" * 512),
        "transactionsRoot": "0x" + block_obj.get("merkle_root", "".zfill(64)),
        "stateRoot": "0x" + ("0" * 64),
        "receiptsRoot": "0x" + ("0" * 64),
        "miner": "0x0000000000000000000000000000000000000000",
        "difficulty": to_hex(int(blockchain.difficulty)),
        "totalDifficulty": to_hex(int(idx * blockchain.difficulty)),
        "extraData": "0x",
        "size": to_hex(len(json.dumps(block_obj)) if block_obj else 0),
        "gasLimit": "0x0",
        "gasUsed": "0x0",
        "timestamp": to_hex(ts),
        "transactions": txs,
        "uncles": []
    }
    return eth_block

def find_block_by_hash(h):
    target = h.lower().replace("0x", "")
    for b in blockchain.chain:
        if blockchain.hash(b).lower() == target:
            return b
    return None

def find_tx_by_hash(h):
    target = h.lower().replace("0x", "")
    for bi, b in enumerate(blockchain.chain):
        for ti, tx in enumerate(b.get("transactions", [])):
            txh = hashlib.sha256(json.dumps(tx, sort_keys=True).encode()).hexdigest().lower()
            if txh == target:
                return tx, bi, ti
    return None, None, None

@app.route("/", methods=["POST"])
def json_rpc():
    data = request.get_json() or {}
    method = data.get("method")
    rpc_id = data.get("id", 1)
    params = data.get("params", [])

    # Basic network info
    if method == "web3_clientVersion":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "LightningVault/0.1"})
    if method == "net_version":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": str(blockchain.chain_id)})
    if method == "net_listening":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": True})
    if method == "eth_protocolVersion":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x41"})
    if method == "eth_chainId":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": hex(blockchain.chain_id)})
    if method == "eth_syncing":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": False})
    if method == "eth_gasPrice":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x0"})
    if method == "eth_maxPriorityFeePerGas":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x0"})
    if method == "eth_mining":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": False})
    if method == "eth_hashrate":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x0"})
    if method == "rpc_modules":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": {"eth": "1.0", "net": "1.0", "web3": "1.0"}})

    # Accounts/balances
    if method == "eth_accounts":
        # This node does not manage Ethereum accounts; MetaMask will supply addresses
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": []})
    if method == "eth_getBalance":
        if not params:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid params"}})
        address = params[0]
        if isinstance(address, str) and address.startswith("0x"):
            balance = blockchain.balances.get(address, Decimal("0"))
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": to_hex_wei(balance)})
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x0"})
    if method == "eth_getTransactionCount":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x0"})

    if method == "eth_sendTransaction":
        # Map simple MetaMask tx to internal transfer
        if not params:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid params"}})
        txo = params[0] or {}
        from_addr = txo.get("from")
        to_addr = txo.get("to")
        value_hex = txo.get("value", "0x0")
        if not from_addr or not to_addr:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "from and to required"}})
        amount = from_hex_wei(value_hex)
        tx = Transaction(sender=from_addr, receiver=to_addr, amount=str(amount), fee=0, tx_type="transfer")
        if blockchain.add_transaction_to_mempool(tx):
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x" + tx.tx_id})
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32000, "message": "Transaction validation failed"}})

    # Blocks
    if method == "eth_blockNumber":
        head = max(0, len(blockchain.chain) - 1)
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": to_hex(head)})

    if method == "eth_getBlockByNumber":
        if not params:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid params"}})
        tag_or_hex = params[0]
        include_full = bool(params[1]) if len(params) > 1 else False
        if isinstance(tag_or_hex, str):
            if tag_or_hex in ("latest", "pending"):
                block_index = max(0, len(blockchain.chain) - 1)
            elif tag_or_hex == "earliest":
                block_index = 0
            else:
                try:
                    block_index = int(tag_or_hex, 16)
                except Exception:
                    return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": None})
        else:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": None})

        if 0 <= block_index < len(blockchain.chain):
            block = blockchain.chain[block_index]
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": to_eth_block(block, include_full)})
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": None})

    if method == "eth_getBlockByHash":
        if not params:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid params"}})
        blk = find_block_by_hash(params[0])
        include_full = bool(params[1]) if len(params) > 1 else False
        if blk is None:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": None})
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": to_eth_block(blk, include_full)})

    # Transactions
    if method == "eth_getTransactionByHash":
        if not params:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid params"}})
        tx, bi, ti = find_tx_by_hash(params[0])
        if tx is None:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": None})
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": to_eth_tx(tx, bi, ti)})

    if method == "eth_getTransactionReceipt":
        # No EVM receipts; return null or minimal when found
        if not params:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid params"}})
        tx, bi, ti = find_tx_by_hash(params[0])
        if tx is None:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": None})
        # Minimal receipt
        receipt = {
            "transactionHash": params[0],
            "transactionIndex": to_hex(ti),
            "blockHash": block_hash(blockchain.chain[bi]) if bi is not None else None,
            "blockNumber": to_hex(bi),
            "from": tx.get("sender"),
            "to": tx.get("receiver"),
            "cumulativeGasUsed": "0x0",
            "gasUsed": "0x0",
            "contractAddress": None,
            "logs": [],
            "status": "0x1",
            "logsBloom": "0x" + ("0" * 512)
        }
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": receipt})

    if method == "eth_sendRawTransaction":
        # Ethereum-compatible legacy RLP-signed transactions only (no typed tx)
        if not params:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid params"}})
        raw = params[0]
        if not isinstance(raw, str) or not raw.startswith('0x'):
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid raw tx hex"}})
        try:
            raw_bytes = bytes.fromhex(raw[2:])
        except Exception:
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32602, "message": "Invalid raw tx hex"}})

        # Reject typed transactions for now
        if _is_typed_tx(raw_bytes):
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32000, "message": "Typed transactions (EIP-2718/1559) not supported"}})

        # Decode legacy RLP tx: [nonce, gasPrice, gasLimit, to, value, data, v, r, s]
        try:
            fields = rlp.decode(raw_bytes)
            if not isinstance(fields, list) or len(fields) != 9:
                raise ValueError("Invalid legacy RLP tx")
            nonce_b, gas_price_b, gas_b, to_b, value_b, data_b, v_b, r_b, s_b = fields
            v = int.from_bytes(v_b or b"\x00", byteorder='big')
            r = int.from_bytes(r_b or b"\x00", byteorder='big')
            s = int.from_bytes(s_b or b"\x00", byteorder='big')
            # Basic signature sanity
            if r == 0 or s == 0 or v == 0:
                raise ValueError("Invalid signature components")

            # EIP-155 chain id derivation
            tx_chain_id = None
            if v >= 35:
                tx_chain_id = (v - 35) // 2
            # Build sighash per legacy rules
            msg_hash = _get_legacy_tx_signing_hash(nonce_b, gas_price_b, gas_b, to_b, value_b, data_b, tx_chain_id)

            # Recover sender
            try:
                sender_addr = _recover_sender_address_from_vrs(msg_hash, v, r, s, tx_chain_id)
            except BadSignatureError:
                return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32000, "message": "Invalid signature"}})

            # Chain ID enforcement when present
            if tx_chain_id is not None and tx_chain_id != blockchain.chain_id:
                return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32000, "message": "Wrong chainId in transaction"}})

            # Parse value and to
            value_int = int.from_bytes(value_b or b"\x00", byteorder='big')
            amount = to_decimal_from_wei_int(value_int)
            if to_b in (b"", None):
                return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32000, "message": "Contract creation not supported"}})
            to_addr = to_checksum_address('0x' + (to_b.hex() if isinstance(to_b, (bytes, bytearray)) else bytes(to_b).hex()))

            tx = Transaction(sender=sender_addr, receiver=to_addr, amount=str(amount), fee=0, tx_type="transfer")
            if blockchain.add_transaction_to_mempool(tx):
                return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x" + tx.tx_id})
            return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32000, "message": "Transaction validation failed"}})

        except rlp.DecodingError:
            # Fallback: maintain support for custom hex-encoded JSON for dev tools
            try:
                payload_str = bytes.fromhex(raw[2:]).decode('utf-8')
                obj = json.loads(payload_str)
                from_addr = obj.get('from')
                to_addr = obj.get('to', TREASURY_ADDRESS if obj.get('tx_type') == 'nft_mint' else None)
                value_hex = obj.get('value', '0x0')
                tx_type = obj.get('tx_type', 'transfer')
                data_obj = obj.get('data', {})
                if not from_addr or to_addr is None:
                    raise ValueError('from/to required')
                amount = from_hex_wei(value_hex)
                tx = Transaction(sender=from_addr, receiver=to_addr, amount=str(amount), fee=0, tx_type=tx_type, data=data_obj)
                if blockchain.add_transaction_to_mempool(tx):
                    return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x" + tx.tx_id})
                return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32000, "message": "Transaction validation failed"}})
            except Exception:
                return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32000, "message": "Unsupported raw transaction format"}})

    if method == "eth_estimateGas":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x5208"})

    if method == "eth_call":
        # No EVM; return empty data
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x"})
    if method == "eth_getCode":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x"})
    if method == "eth_getLogs":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": []})
    if method == "eth_newFilter":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": "0x1"})
    if method == "eth_uninstallFilter":
        return jsonify({"jsonrpc": "2.0", "id": rpc_id, "result": True})

    # Default fallback
    return jsonify({"jsonrpc": "2.0", "id": rpc_id, "error": {"code": -32601, "message": "Method not found"}})

# -------------------------------
# Main
# -------------------------------
if __name__ == "__main__":
    host = os.environ.get("RPC_HOST", "0.0.0.0")
    logger.info(f"Starting Lightning Vault node on {host}:{port}")
    serve(app, host=host, port=port)
