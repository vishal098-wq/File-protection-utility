#!/usr/bin/env python3
"""
File Protection Utility (Zero-Dependency / Mobile-friendly version)
---------------------------------------------------------------------
Encrypts/decrypts files using AES-256 in CTR mode with a password-derived
key (PBKDF2-HMAC-SHA256), plus HMAC-SHA256 for MAC integrity verification
(Encrypt-then-MAC construction).

Why this version has NO external dependencies:
Pydroid3 on Android could not install the `cryptography` package without
an extra Play-Store plugin, so this rewrite uses ONLY Python's standard
library:
    - hashlib.pbkdf2_hmac  -> real PBKDF2-HMAC-SHA256 key derivation
    - hmac + hashlib.sha256 -> real HMAC-SHA256 for the MAC/integrity check
    - AES-256 block cipher  -> implemented from scratch below (Python has
      no built-in AES), verified against the official NIST FIPS-197
      Appendix C.3 test vector, then used in CTR mode.

File format written to <name>.enc:
    [MAGIC 4 bytes]["FPU2"]
    [salt   16 bytes]  (for key derivation)
    [nonce  16 bytes]  (CTR mode initial counter block)
    [ciphertext N bytes]
    [HMAC-SHA256 tag 32 bytes]  (covers everything before it)

Decryption re-derives the key, recomputes the HMAC over the received data,
and ONLY proceeds to decrypt if the tag matches (constant-time compare) --
this is the "verifying MAC integrity" step. A wrong password or any
tampering with the file causes decryption to abort with an error and no
plaintext is written.
"""

import getpass
import hashlib
import hmac
import os
import sys

# ======================================================================
# Pure-Python AES-256 block cipher (encryption direction only -- CTR
# mode uses AES-encrypt on both the sending and receiving side).
# Verified against FIPS-197 Appendix C.3 known-answer test.
# ======================================================================

_SBOX = [
0x63,0x7c,0x77,0x7b,0xf2,0x6b,0x6f,0xc5,0x30,0x01,0x67,0x2b,0xfe,0xd7,0xab,0x76,
0xca,0x82,0xc9,0x7d,0xfa,0x59,0x47,0xf0,0xad,0xd4,0xa2,0xaf,0x9c,0xa4,0x72,0xc0,
0xb7,0xfd,0x93,0x26,0x36,0x3f,0xf7,0xcc,0x34,0xa5,0xe5,0xf1,0x71,0xd8,0x31,0x15,
0x04,0xc7,0x23,0xc3,0x18,0x96,0x05,0x9a,0x07,0x12,0x80,0xe2,0xeb,0x27,0xb2,0x75,
0x09,0x83,0x2c,0x1a,0x1b,0x6e,0x5a,0xa0,0x52,0x3b,0xd6,0xb3,0x29,0xe3,0x2f,0x84,
0x53,0xd1,0x00,0xed,0x20,0xfc,0xb1,0x5b,0x6a,0xcb,0xbe,0x39,0x4a,0x4c,0x58,0xcf,
0xd0,0xef,0xaa,0xfb,0x43,0x4d,0x33,0x85,0x45,0xf9,0x02,0x7f,0x50,0x3c,0x9f,0xa8,
0x51,0xa3,0x40,0x8f,0x92,0x9d,0x38,0xf5,0xbc,0xb6,0xda,0x21,0x10,0xff,0xf3,0xd2,
0xcd,0x0c,0x13,0xec,0x5f,0x97,0x44,0x17,0xc4,0xa7,0x7e,0x3d,0x64,0x5d,0x19,0x73,
0x60,0x81,0x4f,0xdc,0x22,0x2a,0x90,0x88,0x46,0xee,0xb8,0x14,0xde,0x5e,0x0b,0xdb,
0xe0,0x32,0x3a,0x0a,0x49,0x06,0x24,0x5c,0xc2,0xd3,0xac,0x62,0x91,0x95,0xe4,0x79,
0xe7,0xc8,0x37,0x6d,0x8d,0xd5,0x4e,0xa9,0x6c,0x56,0xf4,0xea,0x65,0x7a,0xae,0x08,
0xba,0x78,0x25,0x2e,0x1c,0xa6,0xb4,0xc6,0xe8,0xdd,0x74,0x1f,0x4b,0xbd,0x8b,0x8a,
0x70,0x3e,0xb5,0x66,0x48,0x03,0xf6,0x0e,0x61,0x35,0x57,0xb9,0x86,0xc1,0x1d,0x9e,
0xe1,0xf8,0x98,0x11,0x69,0xd9,0x8e,0x94,0x9b,0x1e,0x87,0xe9,0xce,0x55,0x28,0xdf,
0x8c,0xa1,0x89,0x0d,0xbf,0xe6,0x42,0x68,0x41,0x99,0x2d,0x0f,0xb0,0x54,0xbb,0x16]

_RCON = [0x01,0x02,0x04,0x08,0x10,0x20,0x40,0x80,0x1b,0x36,0x6c,0xd8,0xab,0x4d]


def _xtime(a):
    a <<= 1
    if a & 0x100:
        a ^= 0x11b
    return a & 0xff


def _key_expansion_256(key):
    Nk, Nb, Nr = 8, 4, 14
    w = [list(key[4 * i:4 * i + 4]) for i in range(Nk)]
    for i in range(Nk, Nb * (Nr + 1)):
        temp = list(w[i - 1])
        if i % Nk == 0:
            temp = temp[1:] + temp[:1]
            temp = [_SBOX[b] for b in temp]
            temp[0] ^= _RCON[i // Nk - 1]
        elif Nk > 6 and i % Nk == 4:
            temp = [_SBOX[b] for b in temp]
        w.append([w[i - Nk][j] ^ temp[j] for j in range(4)])
    round_keys = []
    for r in range(Nr + 1):
        rk = []
        for c in range(4):
            rk.extend(w[r * 4 + c])
        round_keys.append(rk)
    return round_keys, Nr


def _add_round_key(state, rk):
    return [state[i] ^ rk[i] for i in range(16)]


def _sub_bytes(state):
    return [_SBOX[b] for b in state]


def _shift_rows(state):
    s = state
    return [
        s[0], s[5], s[10], s[15],
        s[4], s[9], s[14], s[3],
        s[8], s[13], s[2], s[7],
        s[12], s[1], s[6], s[11],
    ]


def _mix_columns(state):
    out = [0] * 16
    for c in range(4):
        col = state[4 * c:4 * c + 4]
        out[4*c+0] = _xtime(col[0]) ^ (_xtime(col[1]) ^ col[1]) ^ col[2] ^ col[3]
        out[4*c+1] = col[0] ^ _xtime(col[1]) ^ (_xtime(col[2]) ^ col[2]) ^ col[3]
        out[4*c+2] = col[0] ^ col[1] ^ _xtime(col[2]) ^ (_xtime(col[3]) ^ col[3])
        out[4*c+3] = (_xtime(col[0]) ^ col[0]) ^ col[1] ^ col[2] ^ _xtime(col[3])
    return out


class AES256:
    """AES-256 single-block encryptor (used as a keystream generator for CTR mode)."""

    def __init__(self, key: bytes):
        if len(key) != 32:
            raise ValueError("AES-256 key must be 32 bytes")
        self.round_keys, self.Nr = _key_expansion_256(key)

    def encrypt_block(self, block16: bytes) -> bytes:
        state = list(block16)
        state = _add_round_key(state, self.round_keys[0])
        for rnd in range(1, self.Nr):
            state = _sub_bytes(state)
            state = _shift_rows(state)
            state = _mix_columns(state)
            state = _add_round_key(state, self.round_keys[rnd])
        state = _sub_bytes(state)
        state = _shift_rows(state)
        state = _add_round_key(state, self.round_keys[self.Nr])
        return bytes(state)


def aes256_ctr_crypt(key: bytes, nonce16: bytes, data: bytes) -> bytes:
    """AES-256-CTR: XORs data with an AES keystream. Same function encrypts
    and decrypts (XOR is its own inverse), like all CTR-mode implementations."""
    aes = AES256(key)
    out = bytearray()
    counter = int.from_bytes(nonce16, "big")
    block_index = 0
    for offset in range(0, len(data), 16):
        counter_block = ((counter + block_index) % (2 ** 128)).to_bytes(16, "big")
        keystream = aes.encrypt_block(counter_block)
        chunk = data[offset:offset + 16]
        out.extend(b ^ k for b, k in zip(chunk, keystream))
        block_index += 1
    return bytes(out)


# ======================================================================
# Key derivation (PBKDF2-HMAC-SHA256, via Python's real stdlib implementation)
# and HMAC-SHA256 integrity tag (via Python's real stdlib implementation).
# ======================================================================

SALT_SIZE = 16
NONCE_SIZE = 16
PBKDF2_ITERATIONS = 390_000
MAGIC_HEADER = b"FPU2"
TAG_SIZE = 32  # HMAC-SHA256 output size


def derive_keys(password: str, salt: bytes):
    """Derive a 64-byte master key via PBKDF2, then split it into a
    32-byte AES encryption key and a 32-byte HMAC key."""
    master = hashlib.pbkdf2_hmac(
        "sha256", password.encode("utf-8"), salt, PBKDF2_ITERATIONS, dklen=64
    )
    enc_key = master[:32]
    mac_key = master[32:]
    return enc_key, mac_key


def encrypt_file(input_path: str, output_path: str, password: str) -> None:
    with open(input_path, "rb") as f:
        plaintext = f.read()

    salt = os.urandom(SALT_SIZE)
    nonce = os.urandom(NONCE_SIZE)
    enc_key, mac_key = derive_keys(password, salt)

    ciphertext = aes256_ctr_crypt(enc_key, nonce, plaintext)

    signed_portion = MAGIC_HEADER + salt + nonce + ciphertext
    tag = hmac.new(mac_key, signed_portion, hashlib.sha256).digest()

    with open(output_path, "wb") as f:
        f.write(signed_portion)
        f.write(tag)

    print(f"\n[+] SUCCESS: Encrypted '{input_path}' -> '{output_path}'")
    print(f"    salt: {salt.hex()}")
    print(f"    nonce: {nonce.hex()}")
    print(f"    HMAC tag: {tag.hex()}")


def decrypt_file(input_path: str, output_path: str, password: str) -> None:
    with open(input_path, "rb") as f:
        blob = f.read()

    if len(blob) < 4 + SALT_SIZE + NONCE_SIZE + TAG_SIZE or blob[:4] != MAGIC_HEADER:
        print("\n[!] Not a recognized encrypted file (bad header).")
        return

    salt = blob[4:4 + SALT_SIZE]
    nonce = blob[4 + SALT_SIZE:4 + SALT_SIZE + NONCE_SIZE]
    ciphertext = blob[4 + SALT_SIZE + NONCE_SIZE:-TAG_SIZE]
    received_tag = blob[-TAG_SIZE:]

    enc_key, mac_key = derive_keys(password, salt)

    signed_portion = MAGIC_HEADER + salt + nonce + ciphertext
    expected_tag = hmac.new(mac_key, signed_portion, hashlib.sha256).digest()

    # --- MAC / integrity verification step ---
    if not hmac.compare_digest(expected_tag, received_tag):
        print("\n[!] FAILED: wrong password or file was tampered with (MAC check failed).")
        return

    plaintext = aes256_ctr_crypt(enc_key, nonce, ciphertext)

    with open(output_path, "wb") as f:
        f.write(plaintext)

    print(f"\n[+] SUCCESS: Decrypted '{input_path}' -> '{output_path}'")
    print("    MAC/integrity check: PASSED")


# ======================================================================
# Interactive CLI (no typed commands needed -- just press Run)
# ======================================================================

def main():
    print("=" * 55)
    print(" File Protection Utility  (AES-256-CTR + PBKDF2 + HMAC)")
    print(" [pure Python standard library -- no pip installs needed]")
    print("=" * 55)

    if not os.path.isfile("secret.txt") and not os.path.isfile("secret.txt.enc"):
        with open("secret.txt", "w") as f:
            f.write("This is a secret test document with sensitive data.\n")
        print("[i] Created a demo file: secret.txt")

    print("\nWhat do you want to do?")
    print("  1 = Encrypt a file")
    print("  2 = Decrypt a file")
    choice = input("Enter 1 or 2: ").strip()

    if choice == "1":
        input_path = input("File to encrypt [secret.txt]: ").strip() or "secret.txt"
        if not os.path.isfile(input_path):
            print(f"[!] File not found: {input_path}")
            sys.exit(1)
        output_path = input(f"Output file [{input_path}.enc]: ").strip() or f"{input_path}.enc"
        password = input("Enter password: ")
        encrypt_file(input_path, output_path, password)

    elif choice == "2":
        input_path = input("File to decrypt [secret.txt.enc]: ").strip() or "secret.txt.enc"
        if not os.path.isfile(input_path):
            print(f"[!] File not found: {input_path}")
            sys.exit(1)
        default_out = input_path[:-4] if input_path.endswith(".enc") else input_path + ".dec"
        output_path = input(f"Output file [{default_out}]: ").strip() or default_out
        password = input("Enter password: ")
        decrypt_file(input_path, output_path, password)

    else:
        print("[!] Invalid choice.")


if __name__ == "__main__":
    main()
