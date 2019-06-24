/*
	This file is part of solidity.

	solidity is free software: you can redistribute it and/or modify
	it under the terms of the GNU General Public License as published by
	the Free Software Foundation, either version 3 of the License, or
	(at your option) any later version.

	solidity is distributed in the hope that it will be useful,
	but WITHOUT ANY WARRANTY; without even the implied warranty of
	MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
	GNU General Public License for more details.

	You should have received a copy of the GNU General Public License
	along with solidity.  If not, see <http://www.gnu.org/licenses/>.
*/
/** @file CommonData.cpp
 * @author Gav Wood <i@gavwood.com>
 * @date 2014
 */

#include <libdevcore/CommonData.h>
#include <libdevcore/Exceptions.h>
#include <libdevcore/Assertions.h>
#include "libdevcore/keccak.h"
#include <libdevcore/Keccak256.h>

#include <boost/algorithm/string.hpp>

// big endian architectures need #define __BYTE_ORDER __BIG_ENDIAN
#ifndef _MSC_VER
#include <endian.h>
#endif

using namespace std;
using namespace dev;

string dev::toHex(bytes const& _data, HexPrefix _prefix, HexCase _case)
{
	std::ostringstream ret;
	if (_prefix == HexPrefix::Add)
		ret << "0x";

	int rix = _data.size() - 1;
	for (uint8_t c: _data)
	{
		// switch hex case every four hexchars
		auto hexcase = std::nouppercase;
		if (_case == HexCase::Upper)
			hexcase = std::uppercase;
		else if (_case == HexCase::Mixed)
			hexcase = (rix-- & 2) == 0 ? std::nouppercase : std::uppercase;

		ret << std::hex << hexcase << std::setfill('0') << std::setw(2) << size_t(c);
	}

	return ret.str();
}

int dev::fromHex(char _i, WhenError _throw)
{
	if (_i >= '0' && _i <= '9')
		return _i - '0';
	if (_i >= 'a' && _i <= 'f')
		return _i - 'a' + 10;
	if (_i >= 'A' && _i <= 'F')
		return _i - 'A' + 10;
	if (_throw == WhenError::Throw)
		BOOST_THROW_EXCEPTION(BadHexCharacter() << errinfo_invalidSymbol(_i));
	else
		return -1;
}

bytes dev::fromHex(std::string const& _s, WhenError _throw)
{
	unsigned s = (_s.size() >= 2 && _s[0] == '0' && _s[1] == 'x') ? 2 : 0;
	std::vector<uint8_t> ret;
	ret.reserve((_s.size() - s + 1) / 2);

	if (_s.size() % 2)
	{
		int h = fromHex(_s[s++], WhenError::DontThrow);
		if (h != -1)
			ret.push_back(h);
		else if (_throw == WhenError::Throw)
			BOOST_THROW_EXCEPTION(BadHexCharacter());
		else
			return bytes();
	}
	for (unsigned i = s; i < _s.size(); i += 2)
	{
		int h = fromHex(_s[i], WhenError::DontThrow);
		int l = fromHex(_s[i + 1], WhenError::DontThrow);
		if (h != -1 && l != -1)
			ret.push_back((uint8_t)(h * 16 + l));
		else if (_throw == WhenError::Throw)
			BOOST_THROW_EXCEPTION(BadHexCharacter());
		else
			return bytes();
	}
	return ret;
}


bool dev::passesAddressChecksum(string const& _str, bool _strict)
{
	string s = _str.substr(0, 2) == "0x" ? _str : "0x" + _str;

	if (s.length() != 42)
		return false;

	if (!_strict && (
		s.find_first_of("abcdef") == string::npos ||
		s.find_first_of("ABCDEF") == string::npos
	))
		return true;

	return s == dev::getChecksummedAddress(s);
}

Keccak digestKeccak(Keccak::Keccak256);
const size_t BufferSize = 144*7*1024;
char* buffer = new char[BufferSize];
std::istream* input = NULL;


/// same as reset()
Keccak::Keccak(Bits bits)
: m_blockSize(200 - 2 * (bits / 8)),
  m_bits(bits)
{
  reset();
}


/// restart
void Keccak::reset()
{
  for (size_t i = 0; i < StateSize; i++)
    m_hash[i] = 0;

  m_numBytes   = 0;
  m_bufferSize = 0;
}


/// constants and local helper functions
namespace
{
  const unsigned int KeccakRounds = 24;
  const uint64_t XorMasks[KeccakRounds] =
  {
    0x0000000000000001ULL, 0x0000000000008082ULL, 0x800000000000808aULL,
    0x8000000080008000ULL, 0x000000000000808bULL, 0x0000000080000001ULL,
    0x8000000080008081ULL, 0x8000000000008009ULL, 0x000000000000008aULL,
    0x0000000000000088ULL, 0x0000000080008009ULL, 0x000000008000000aULL,
    0x000000008000808bULL, 0x800000000000008bULL, 0x8000000000008089ULL,
    0x8000000000008003ULL, 0x8000000000008002ULL, 0x8000000000000080ULL,
    0x000000000000800aULL, 0x800000008000000aULL, 0x8000000080008081ULL,
    0x8000000000008080ULL, 0x0000000080000001ULL, 0x8000000080008008ULL
  };

  /// rotate left and wrap around to the right
  inline uint64_t rotateLeft(uint64_t x, uint8_t numBits)
  {
    return (x << numBits) | (x >> (64 - numBits));
  }

  /// convert litte vs big endian
  inline uint64_t swap(uint64_t x)
  {
#if defined(__GNUC__) || defined(__clang__)
    return __builtin_bswap64(x);
#endif
#ifdef _MSC_VER
    return _byteswap_uint64(x);
#endif

    return  (x >> 56) |
           ((x >> 40) & 0x000000000000FF00ULL) |
           ((x >> 24) & 0x0000000000FF0000ULL) |
           ((x >>  8) & 0x00000000FF000000ULL) |
           ((x <<  8) & 0x000000FF00000000ULL) |
           ((x << 24) & 0x0000FF0000000000ULL) |
           ((x << 40) & 0x00FF000000000000ULL) |
            (x << 56);
  }


  /// return x % 5 for 0 <= x <= 9
  unsigned int mod5(unsigned int x)
  {
    if (x < 5)
      return x;

    return x - 5;
  }
}


/// process a full block
void Keccak::processBlock(const void* data)
{
#if defined(__BYTE_ORDER) && (__BYTE_ORDER != 0) && (__BYTE_ORDER == __BIG_ENDIAN)
#define LITTLEENDIAN(x) swap(x)
#else
#define LITTLEENDIAN(x) (x)
#endif

  const uint64_t* data64 = (const uint64_t*) data;
  // mix data into state
  for (unsigned int i = 0; i < m_blockSize / 8; i++)
    m_hash[i] ^= LITTLEENDIAN(data64[i]);

  // re-compute state
  for (unsigned int round = 0; round < KeccakRounds; round++)
  {
    // Theta
    uint64_t coefficients[5];
    for (unsigned int i = 0; i < 5; i++)
      coefficients[i] = m_hash[i] ^ m_hash[i + 5] ^ m_hash[i + 10] ^ m_hash[i + 15] ^ m_hash[i + 20];

    for (unsigned int i = 0; i < 5; i++)
    {
      uint64_t one = coefficients[mod5(i + 4)] ^ rotateLeft(coefficients[mod5(i + 1)], 1);
      m_hash[i     ] ^= one;
      m_hash[i +  5] ^= one;
      m_hash[i + 10] ^= one;
      m_hash[i + 15] ^= one;
      m_hash[i + 20] ^= one;
    }

    // temporary
    uint64_t one;

    // Rho Pi
    uint64_t last = m_hash[1];
    one = m_hash[10]; m_hash[10] = rotateLeft(last,  1); last = one;
    one = m_hash[ 7]; m_hash[ 7] = rotateLeft(last,  3); last = one;
    one = m_hash[11]; m_hash[11] = rotateLeft(last,  6); last = one;
    one = m_hash[17]; m_hash[17] = rotateLeft(last, 10); last = one;
    one = m_hash[18]; m_hash[18] = rotateLeft(last, 15); last = one;
    one = m_hash[ 3]; m_hash[ 3] = rotateLeft(last, 21); last = one;
    one = m_hash[ 5]; m_hash[ 5] = rotateLeft(last, 28); last = one;
    one = m_hash[16]; m_hash[16] = rotateLeft(last, 36); last = one;
    one = m_hash[ 8]; m_hash[ 8] = rotateLeft(last, 45); last = one;
    one = m_hash[21]; m_hash[21] = rotateLeft(last, 55); last = one;
    one = m_hash[24]; m_hash[24] = rotateLeft(last,  2); last = one;
    one = m_hash[ 4]; m_hash[ 4] = rotateLeft(last, 14); last = one;
    one = m_hash[15]; m_hash[15] = rotateLeft(last, 27); last = one;
    one = m_hash[23]; m_hash[23] = rotateLeft(last, 41); last = one;
    one = m_hash[19]; m_hash[19] = rotateLeft(last, 56); last = one;
    one = m_hash[13]; m_hash[13] = rotateLeft(last,  8); last = one;
    one = m_hash[12]; m_hash[12] = rotateLeft(last, 25); last = one;
    one = m_hash[ 2]; m_hash[ 2] = rotateLeft(last, 43); last = one;
    one = m_hash[20]; m_hash[20] = rotateLeft(last, 62); last = one;
    one = m_hash[14]; m_hash[14] = rotateLeft(last, 18); last = one;
    one = m_hash[22]; m_hash[22] = rotateLeft(last, 39); last = one;
    one = m_hash[ 9]; m_hash[ 9] = rotateLeft(last, 61); last = one;
    one = m_hash[ 6]; m_hash[ 6] = rotateLeft(last, 20); last = one;
                      m_hash[ 1] = rotateLeft(last, 44);

    // Chi
    for (unsigned int j = 0; j < 25; j += 5)
    {
      // temporaries
      uint64_t one = m_hash[j];
      uint64_t two = m_hash[j + 1];

      m_hash[j]     ^= m_hash[j + 2] & ~two;
      m_hash[j + 1] ^= m_hash[j + 3] & ~m_hash[j + 2];
      m_hash[j + 2] ^= m_hash[j + 4] & ~m_hash[j + 3];
      m_hash[j + 3] ^=      one      & ~m_hash[j + 4];
      m_hash[j + 4] ^=      two      & ~one;
    }

    // Iota
    m_hash[0] ^= XorMasks[round];
  }
}


/// add arbitrary number of bytes
void Keccak::add(const void* data, size_t numBytes)
{
  const uint8_t* current = (const uint8_t*) data;

  if (m_bufferSize > 0)
  {
    while (numBytes > 0 && m_bufferSize < m_blockSize)
    {
      m_buffer[m_bufferSize++] = *current++;
      numBytes--;
    }
  }

  // full buffer
  if (m_bufferSize == m_blockSize)
  {
    processBlock((void*)m_buffer);
    m_numBytes  += m_blockSize;
    m_bufferSize = 0;
  }

  // no more data ?
  if (numBytes == 0)
    return;

  // process full blocks
  while (numBytes >= m_blockSize)
  {
    processBlock(current);
    current    += m_blockSize;
    m_numBytes += m_blockSize;
    numBytes   -= m_blockSize;
  }

  // keep remaining bytes in buffer
  while (numBytes > 0)
  {
    m_buffer[m_bufferSize++] = *current++;
    numBytes--;
  }
}


/// process everything left in the internal buffer
void Keccak::processBuffer()
{
  unsigned int blockSize = 200 - 2 * (m_bits / 8);

  // add padding
  size_t offset = m_bufferSize;
  // add a "1" byte
  m_buffer[offset++] = 1;
  // fill with zeros
  while (offset < blockSize)
    m_buffer[offset++] = 0;

  // and add a single set bit
  m_buffer[blockSize - 1] |= 0x80;

  processBlock(m_buffer);
}


/// return latest hash as 16 hex characters
std::string Keccak::getHash()
{
  // process remaining bytes
  processBuffer();

  // convert hash to string
  static const char dec2hex[16 + 1] = "0123456789abcdef";

  // number of significant elements in hash (uint64_t)
  unsigned int hashLength = m_bits / 64;

  std::string result;
  for (unsigned int i = 0; i < hashLength; i++)
    for (unsigned int j = 0; j < 8; j++) // 64 bits => 8 bytes
    {
      // convert a byte to hex
      unsigned char oneByte = (unsigned char) (m_hash[i] >> (8 * j));
      result += dec2hex[oneByte >> 4];
      result += dec2hex[oneByte & 15];
    }

  // Keccak224's last entry in m_hash provides only 32 bits instead of 64 bits
  unsigned int remainder = m_bits - hashLength * 64;
  unsigned int processed = 0;
  while (processed < remainder)
  {
    // convert a byte to hex
    unsigned char oneByte = (unsigned char) (m_hash[hashLength] >> processed);
    result += dec2hex[oneByte >> 4];
    result += dec2hex[oneByte & 15];

    processed += 8;
  }

  return result;
}


/// compute Keccak hash of a memory block
std::string Keccak::operator()(const void* data, size_t numBytes)
{
  reset();
  add(data, numBytes);
  return getHash();
}


/// compute Keccak hash of a string, excluding final zero
std::string Keccak::operator()(const std::string& text)
{
  reset();
  add(text.c_str(), text.size());
  return getHash();
}






string dev::getChecksummedAddress(string const& _addr)
{
	std::cout << "getChecksummedAddress addr - " << _addr << std::endl;
	string s = _addr.substr(0, 2) == "0x" ? _addr.substr(2) : _addr;
	assertThrow(s.length() == 40, InvalidAddress, "");
	assertThrow(s.find_first_not_of("0123456789abcdefABCDEF") == string::npos, InvalidAddress, "");
	
	//h256 hash = keccak256(boost::algorithm::to_lower_copy(s, std::locale::classic()));
	//input=s.c_str();
	//(s.c_str())->read(buffer, BufferSize);
	std::copy(s.begin(), s.end(), buffer);
	std::size_t numBytesRead = size_t(input->gcount());
	digestKeccak.add(buffer, numBytesRead);
	h256 hash = keccak256(boost::algorithm::to_lower_copy(digestKeccak.getHash(),std::locale::classic()));

	std::cout << "getChecksummedAddress hash - " << digestKeccak.getHash() << std::endl;
	string ret = "0x";
	for (size_t i = 0; i < 40; ++i)
	{
		char addressCharacter = s[i];
		unsigned nibble = (unsigned(hash[i / 2]) >> (4 * (1 - (i % 2)))) & 0xf;
		if (nibble >= 8)
			ret += toupper(addressCharacter);
		else
			ret += tolower(addressCharacter);
	}
	return ret;
}

bool dev::isValidHex(string const& _string)
{
	if (_string.substr(0, 2) != "0x")
		return false;
	if (_string.find_first_not_of("0123456789abcdefABCDEF", 2) != string::npos)
		return false;
	return true;
}

bool dev::isValidDecimal(string const& _string)
{
	if (_string.empty())
		return false;
	if (_string == "0")
		return true;
	// No leading zeros
	if (_string.front() == '0')
		return false;
	if (_string.find_first_not_of("0123456789") != string::npos)
		return false;
	return true;
}
