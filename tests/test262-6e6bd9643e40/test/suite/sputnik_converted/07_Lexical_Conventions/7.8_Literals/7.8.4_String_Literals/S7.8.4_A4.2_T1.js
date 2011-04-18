// Copyright 2009 the Sputnik authors.  All rights reserved.
// This code is governed by the BSD license found in the LICENSE file.

/**
 * @name: S7.8.4_A4.2_T1;
 * @section: 7.8.4;
 * @assertion: CharacterEscapeSequnce :: NonEscapeSequence;  
 * @description: NonEscapeSequence :: ENGLISH CAPITAL ALPHABET;
*/


// Converted for Test262 from original Sputnik source

ES5Harness.registerTest( {
id: "S7.8.4_A4.2_T1",

path: "7.8.4",

description: "NonEscapeSequence :: ENGLISH CAPITAL ALPHABET",

test: function testcase() {
   //CHECK#A-Z
CharacterCode = [0x0041, 0x0042, 0x0043, 0x0044, 0x0045, 0x0046, 0x0047, 0x0048, 0x0049, 0x004A, 0x004B, 0x004C, 0x004D, 0x004E, 0x004F, 0x0050, 0x0051, 0x0052, 0x0053, 0x0054, 0x0055, 0x0056, 0x0057, 0x0058, 0x0059, 0x005A];
NonEscapeCharacter = ["\A", "\B", "\C", "\D", "\E", "\F", "\G", "\H", "\I", "\J", "\K", "\L", "\M", "\N", "\O", "\P", "\Q", "\R", "\S", "\T", "\U", "\V", "\W", "\X", "\Y", "\Z"];
for (index = 0; index <= 25; index++) {
  if (String.fromCharCode(CharacterCode[index]) !== NonEscapeCharacter[index]) {
    $ERROR('#' + NonEscapeCharacter[index] + ' ');
  }
}

 }
});

