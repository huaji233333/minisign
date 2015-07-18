
Minisign
========

Minisign is a dead simple tool to sign files and verify signatures.

For more information, please refer to the
[Minisign documentation](https://jedisct1.github.io/minisign/)

Tarballs and pre-compiled binaries for Windows and OSX can be verified with
the following public key:

    RWQf6LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3

Compilation / installation
--------------------------

Dependencies:
* [libsodium](http://doc.libsodium.org/)
* cmake

Compilation:

    $ mkdir build
    $ cd build
    $ cmake ..
    $ make
    # make install

Creating a key pair
-------------------

    $ minisign -G

The public key is printed and put into the `minisign.pub` file. The secret key
is encrypted and saved as `minisign.key` file.

Signing a file
--------------

    $ minisign -Sm myfile.txt

Or to include a comment in the signature, that will be verified and
displayed when verifying the file:

    $ minisign -Sm myfile.txt -t 'This comment will be signed as well'

The signature is put into `myfile.txt.minisig`.

Verifying a file
----------------

    $ minisign -Vm myfile.txt -P RWQf6LRCGA9i53mlYecO4IzT51TGPpvWucNSCh1CBM0QTaLn73Y7GFO3

or

    $ minisign -Vm myfile.txt -p signature.pub

This requires the signature `myfile.txt.minisig` to be present in the same
directory.

The public key can either reside in a file (`./minisign.pub` by default) or be
directly specified on the command line.

Usage
-----

    $ minisign -G [-p pubkey] [-s seckey]
    $ minisign -S [-x sigfile] [-s seckey] [-c untrusted_comment] [-t trusted_comment] -m file
    $ minisign -V [-x sigfile] [-p pubkeyfile | -P pubkey] [-q] -m file

    -G                generate a new key pair
    -S                sign a file
    -V                verify that a signature is valid for a given file
    -m <file>         file to sign/verify
    -p <pubkeyfile>   public key file (default: ./minisign.pub)
    -P <pubkey>       public key, as a base64 string
    -s <seckey>       secret key file (default: ./minisign.key)
    -x <sigfile>      signature file (default: <file>.minisig)
    -c <comment>      add a one-line untrusted comment
    -t <comment>      add a one-line trusted comment
    -q                quiet mode, suppress output
    -v                display version number

Trusted comments
----------------

Signature files include an untrusted comment line that can be freely
modified, even after signature creation.

They also include a second comment line, that cannot be modified
without the secret key.

Trusted comments can be used to add instructions or application-specific
metadata (intended file name, timestamps, resource identifiers,
version numbers to prevent downgrade attacks).

Compatibility with OpenBSD signify
----------------------------------

Signature written by minisign can be verified using OpenBSD's signify
tool: public key files and signature files are compatible.

However, minisign uses a slightly different format to store secret keys.

Minisign signatures include trusted comments in addition to untrusted
comments. Trusted comments are signed, thus verified, before being
displayed.

This adds two lines to the signature files, that signify silently ignores.

Signature format
----------------

    untrusted comment: <arbitrary text>
    base64(<signature_algorithm> || <key_id> || <signature>)
    trusted_comment: <arbitrary text>
    base64(<global_signature>)

* `signature_algorithm`: `Ed`
* `key_id`: 8 random bytes, matching the public key
* `signature`: `ed25519(<file data>)`
* `global_signature`: `ed25519(<signature> || <trusted_comment>)`

Public key format
-----------------

    untrusted comment: <arbitrary text>
    base64(<signature_algorithm> || <key_id> || <public_key>)

* `signature_algorithm`: `Ed`
* `key_id`: 8 random bytes
* `public_key`: Ed25519 public key

Secret key format
-----------------

    untrusted comment: <arbitrary text>
    base64(<signature_algorithm> || <kdf_algorithm> || <cksum_algorithm> ||
           <kdf_salt> || <kdf_opslimit> || <kdf_memlimit> || <keynum_sk>)

* `signature_algorithm`: `Ed`
* `kdf_algorithm`: `Sc`
* `cksum_algorithm`: `B2`
* `kdf_salt`: 32 random bytes
* `kdf_opslimit`: `crypto_pwhash_scryptsalsa208sha256_OPSLIMIT_SENSITIVE`
* `kdf_memlimit`: `crypto_pwhash_scryptsalsa208sha256_MEMLIMIT_SENSITIVE`
* `keynum_sk`: `<kdf_output> ^ (<key_id> || secret_key> || <checksum>)`
* `key_id`: 8 random bytes
* `secret_key`: Ed25519 secret key
* `checksum`: `Blake2b(<signature_algorithm> || <key_id> || <secret_key>)`, 32 bytes