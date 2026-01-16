/*
 * ESP-RFID-Tool
 * by Corey Harding of www.Exploit.Agency / www.LegacySecurityGroup.com
 * ESP-RFID-Tool Software is distributed under the MIT License. The license and copyright notice can not be removed and must be distributed alongside all future copies of the software.
 * MIT License
    
    Copyright (c) [2018] [Corey Harding]
    
    Permission is hereby granted, free of charge, to any person obtaining a copy
    of this software and associated documentation files (the "Software"), to deal
    in the Software without restriction, including without limitation the rights
    to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
    copies of the Software, and to permit persons to whom the Software is
    furnished to do so, subject to the following conditions:
    
    The above copyright notice and this permission notice shall be included in all
    copies or substantial portions of the Software.
    
    THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
    FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
    AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
    LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
    OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
    SOFTWARE.
*/
#include "HelpText.h"
#include "License.h"
#include "version.h"
#include "strrev.h"
#include "aba2str.h"
#include <ESP8266WiFi.h>
#include <WiFiClient.h>
#include <ESP8266WebServer.h>
#include <ESP8266HTTPClient.h>
#include <ESP8266httpUpdate.h>
#include <ESP8266HTTPUpdateServer.h>
#include <ESP8266mDNS.h>
#include <FS.h>
#include <ArduinoJson.h> // ArduinoJson library 6.19.4 by Benoit Blanchon https://github.com/bblanchon/ArduinoJson
#include <ESP8266FtpServer.h> // https://github.com/exploitagency/esp8266FTPServer/tree/feature/bbx10_speedup
#include <DNSServer.h>
#include <ESP8266mDNS.h>

#define DATA0 14
#define DATA1 12

#define LED_BUILTIN 2
#define RESTORE_DEFAULTS_PIN 4 //GPIO 4
int jumperState = 0; //For restoring default settings
#include "WiegandNG.h" //https://github.com/jpliew/Wiegand-NG-Multi-Bit-Wiegand-Library-for-Arduino

// Port for web server
ESP8266WebServer server(80);
ESP8266WebServer httpServer(1337);
ESP8266HTTPUpdateServer httpUpdater;
FtpServer ftpSrv;
const byte DNS_PORT = 53;
DNSServer dnsServer;

HTTPClient http;

const char* update_path = "/update";
int accesspointmode;
char ssid[32];
char password[64];
int channel;
int hidden;
char local_IPstr[16];
char gatewaystr[16];
char subnetstr[16];
char update_username[32];
char update_password[64];
char ftp_username[32];
char ftp_password[64];
int ftpenabled;
int ledenabled;
char logname[31];
unsigned int bufferlength;
unsigned int rxpacketgap;
int txdelayus;
int txdelayms;
int safemode;

int dos=0;
int TXstatus=0;
String pinHTML;

#include "pinSEND.h"

String dataCONVERSION="";

WiegandNG wg;

void LogWiegand(WiegandNG &tempwg) {
  volatile unsigned char *buffer=tempwg.getRawData();
  unsigned int bufferSize = tempwg.getBufferSize();
  unsigned int countedBits = tempwg.getBitCounted();

  unsigned int countedBytes = (countedBits/8);
  if ((countedBits % 8)>0) countedBytes++;
  //unsigned int bitsUsed = countedBytes * 8;

  bool binChunk2exists=false;
  volatile unsigned long cardChunk1 = 0;
  volatile unsigned long cardChunk2 = 0;
  volatile unsigned long binChunk2 = 0;
  volatile unsigned long binChunk1 = 0;
  String binChunk3="";
  bool unknown=false;
  binChunk2exists=false;
  int binChunk2len=0;
  int j=0;
  
  for (unsigned int i=bufferSize-countedBytes; i< bufferSize;i++) {
    unsigned char bufByte=buffer[i];
    for(int x=0; x<8;x++) {
      if ( (((bufferSize-i) *8)-x) <= countedBits) {
        j++;
        if((bufByte & 0x80)) {  //write 1
          if(j<23) {
            binChunk1 = binChunk1 << 1;
            binChunk1 |= 1;
          }
          else if(j<=52) {
            binChunk2exists=true;
            binChunk2len++;
            binChunk2 = binChunk2 << 1;
            binChunk2 |= 1;
          }
          else if(j>52){
            binChunk3=binChunk3+"1";
          }
        }
        else {  //write 0
          if(j<23) {
            binChunk1 = binChunk1 << 1;
          }
          else if(j<=52){
            binChunk2exists=true;
            binChunk2len++;
            binChunk2 = binChunk2 << 1;
          }
          else if(j>52){
            binChunk3=binChunk3+"0";
          }
        }
      }
      bufByte<<=1;
    }
  }
  j=0;

  switch (countedBits) {  //Add the preamble to known cards
    case 26:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 2){
          bitWrite(cardChunk1, i, 1); // Write preamble 1's to the 13th and 2nd bits
        }
        else if(i > 2) {
          bitWrite(cardChunk1, i, 0); // Write preamble 0's to all other bits above 1
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 20)); // Write remaining bits to cardChunk1 from binChunk1
        }
        if(i < 20) {
          bitWrite(cardChunk2, i + 4, bitRead(binChunk1, i)); // Write the remaining bits of binChunk1 to cardChunk2
        }
        if(i < 4) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i)); // Write the remaining bit of cardChunk2 with binChunk2 bits
        }
      }
      break;
    case 27:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 3){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 3) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 19));
        }
        if(i < 19) {
          bitWrite(cardChunk2, i + 5, bitRead(binChunk1, i));
        }
        if(i < 5) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 28:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 4){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 4) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 18));
        }
        if(i < 18) {
          bitWrite(cardChunk2, i + 6, bitRead(binChunk1, i));
        }
        if(i < 6) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 29:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 5){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 5) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 17));
        }
        if(i < 17) {
          bitWrite(cardChunk2, i + 7, bitRead(binChunk1, i));
        }
        if(i < 7) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 30:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 6){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 6) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 16));
        }
        if(i < 16) {
          bitWrite(cardChunk2, i + 8, bitRead(binChunk1, i));
        }
        if(i < 8) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 31:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 7){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 7) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 15));
        }
        if(i < 15) {
          bitWrite(cardChunk2, i + 9, bitRead(binChunk1, i));
        }
        if(i < 9) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 32:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 8){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 8) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 14));
        }
        if(i < 14) {
          bitWrite(cardChunk2, i + 10, bitRead(binChunk1, i));
        }
        if(i < 10) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 33:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 9){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 9) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 13));
        }
        if(i < 13) {
          bitWrite(cardChunk2, i + 11, bitRead(binChunk1, i));
        }
        if(i < 11) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 34:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 10){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 10) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 12));
        }
        if(i < 12) {
          bitWrite(cardChunk2, i + 12, bitRead(binChunk1, i));
        }
        if(i < 12) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 35:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 11){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 11) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 11));
        }
        if(i < 11) {
          bitWrite(cardChunk2, i + 13, bitRead(binChunk1, i));
        }
        if(i < 13) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 36:
      for(int i = 19; i >= 0; i--) {
        if(i == 13 || i == 12){
          bitWrite(cardChunk1, i, 1);
        }
        else if(i > 12) {
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 10));
        }
        if(i < 10) {
          bitWrite(cardChunk2, i + 14, bitRead(binChunk1, i));
        }
        if(i < 14) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    case 37:
      for(int i = 19; i >= 0; i--) {
        if(i == 13){
          bitWrite(cardChunk1, i, 0);
        }
        else {
          bitWrite(cardChunk1, i, bitRead(binChunk1, i + 9));
        }
        if(i < 9) {
          bitWrite(cardChunk2, i + 15, bitRead(binChunk1, i));
        }
        if(i < 15) {
          bitWrite(cardChunk2, i, bitRead(binChunk2, i));
        }
      }
      break;
    default:  //unknown card
      unknown=true;
      //String binChunk3 is like cardChunk0
      cardChunk1=binChunk2;
      cardChunk2=binChunk1;
      break;
  }

  //This happens on boot so we filter it.
  if(unknown && countedBits == 2) {
    return;
  }

  File f = SPIFFS.open("/"+String(logname), "a"); //Open the log in append mode to store capture
  int preambleLen;
  if (unknown==true && countedBits!=4 && countedBits!=8 && countedBits!=248) {
    f.print(F("Unknown "));
    preambleLen=0;
  }
  else {
    preambleLen=(44-countedBits);
  }
  
  f.print(String()+countedBits+F(" bit card,"));

  if (countedBits==4||countedBits==8) {
    f.print(F("Possible keypad entry,"));
  }

  if (countedBits==248) {
    f.print(F("possible magstripe card,"));
  }
  String magstripe="";

  if (unknown!=true) {
    f.print(String()+preambleLen+F(" bit preamble,"));
  }
  
  f.print(F("Binary:"));

  //f.print(" ");  //debug line
  if (binChunk2exists==true && unknown!=true) {
    for(int i = (((countedBits+preambleLen)-countedBits)+(countedBits-24)); i--;) {
      if (i==((((countedBits+preambleLen)-countedBits)+(countedBits-24))-preambleLen-1) && unknown!=true) {
        f.print(" ");
      }
      f.print(bitRead(cardChunk1, i));
      if(i == 0){
        break;
      }
    }
  }
  
  if ((countedBits>=24) && unknown!=true) {
    for(int i = 24; i--;) {
      f.print(bitRead(cardChunk2, i));
      if(i == 0){
        break;
      }
    }
  }
  else if ((countedBits>=23) && unknown==true) {
    int i;
    if (countedBits>=52) {
      i=22;
    }
    else {
      i =(countedBits-binChunk2len);
    }
    for(i; i--;) {
      f.print(bitRead(binChunk1, i));
      if (countedBits==248) {
        magstripe+=bitRead(binChunk1, i);
      }
      if(i == 0){
        break;
      }
    }
  }
  else {
    for(int i = countedBits; i--;) {
      f.print(bitRead(binChunk1, i));
      if(i == 0){
        break;
      }
    }
  }

  if (binChunk2exists==true && unknown==true) {
    int i;
    if (countedBits>=52) {
      i=30;
    }
    else {
      i=(binChunk2len);
    }
    for(i; i--;) {
      f.print(bitRead(binChunk2, i));
      if (countedBits==248) {
        magstripe+=bitRead(binChunk2, i);
      }
      if(i == 0){
        break;
      }
    }
  }

  if (countedBits>52) {
    f.print(binChunk3);
    if (countedBits==248) {
        magstripe+=binChunk3;
    }
  }

  if (countedBits<=52 && unknown!=true) {
    f.print(",HEX:");
    if (binChunk2exists==true) {
      f.print(cardChunk1, HEX);
    }
    //f.print(" "); //debug line
    f.println(cardChunk2, HEX);
  }
  else if (countedBits==4||countedBits==8) {
    f.print(",Keypad Code:");
    if (binChunk1 == 0B0000||binChunk1 == 0b11110000) {
      f.print("0");
    }
    else if (binChunk1 == 0B0001||binChunk1 == 0b11100001) {
      f.print("1");
    }
    else if (binChunk1 == 0B0010||binChunk1 == 0b11010010) {
      f.print("2");
    }
    else if (binChunk1 == 0B0011||binChunk1 == 0b11000011) {
      f.print("3");
    }
    else if (binChunk1 == 0B0100||binChunk1 == 0b10110100) {
      f.print("4");
    }
    else if (binChunk1 == 0B0101||binChunk1 == 0b10100101) {
      f.print("5");
    }
    else if (binChunk1 == 0B0110||binChunk1 == 0b10010110) {
      f.print("6");
    }
    else if (binChunk1 == 0B0111||binChunk1 == 0b10000111) {
      f.print("7");
    }
    else if (binChunk1 == 0B1000||binChunk1 == 0b01111000) {
      f.print("8");
    }
    else if (binChunk1 == 0B1001||binChunk1 == 0b01101001) {
      f.print("9");
    }
    else if (binChunk1 == 0B1010||binChunk1 == 0b01011010) {
      f.print("*");
    }
    else if (binChunk1 == 0B1011||binChunk1 == 0b01001011) {
      f.print("#");
    }
    else if (binChunk1 == 0b1100||binChunk1 == 0b00111100) {
      f.print("F1");
    }
    else if (binChunk1 == 0b1101||binChunk1 == 0b00101101) {
      f.print("F2");
    }
    else if (binChunk1 == 0b1110||binChunk1 == 0b00011110) {
      f.print("F3");
    }
    else if (binChunk1 == 0b1111||binChunk1 == 0b00001111) {
      f.print("F4");
    }
    else {
      f.print("?");
    }
    f.print(",HEX:");
    if (countedBits==8) {
      char hexCHAR[3];
      sprintf(hexCHAR, "%02X", binChunk1);
      f.println(hexCHAR);
    }
    else if (countedBits==4) {
      f.println(binChunk1, HEX);
    }
  }
  else if (countedBits==248) {
    f.println(",");
  }
  else {
    f.println("");
  }

  if (countedBits==248) {
    int startSentinel=magstripe.indexOf("11010");
    int endSentinel=(magstripe.lastIndexOf("11111")+4);
    int magStart=0;
    int magEnd=1;
  
    f.print(" * Trying \"Forward\" Swipe,");
    magStart=startSentinel;
    magEnd=endSentinel;
    f.println(aba2str(magstripe,magStart,magEnd,"\"Forward\" Swipe"));
    
    f.print(" * Trying \"Reverse\" Swipe,");
    char magchar[249];
    magstripe.toCharArray(magchar,249);
    magstripe=String(strrev(magchar));
    magStart=magstripe.indexOf("11010");
    magEnd=(magstripe.lastIndexOf("11111")+4);
    f.println(aba2str(magstripe,magStart,magEnd,"\"Reverse\" Swipe"));
  }

  unknown=false;
  binChunk3="";
  binChunk2exists=false;
  binChunk1 = 0; binChunk2 = 0;
  cardChunk1 = 0; cardChunk2 = 0;
  binChunk2len=0;

  f.close();
}

#include "api.h"

void settingsPage()
{
  if(!server.authenticate(update_username, update_password))
    return server.requestAuthentication();
  String accesspointmodeyes;
  String accesspointmodeno;
  if (accesspointmode==1){
    accesspointmodeyes=" checked=\"checked\"";
    accesspointmodeno="";
  }
  else {
    accesspointmodeyes="";
    accesspointmodeno=" checked=\"checked\"";
  }
  String ftpenabledyes;
  String ftpenabledno;
  if (ftpenabled==1){
    ftpenabledyes=" checked=\"checked\"";
    ftpenabledno="";
  }
  else {
    ftpenabledyes="";
    ftpenabledno=" checked=\"checked\"";
  }
  String ledenabledyes;
  String ledenabledno;
  if (ledenabled==1){
    ledenabledyes=" checked=\"checked\"";
    ledenabledno="";
  }
  else {
    ledenabledyes="";
    ledenabledno=" checked=\"checked\"";
  }
  String hiddenyes;
  String hiddenno;
  if (hidden==1){
    hiddenyes=" checked=\"checked\"";
    hiddenno="";
  }
  else {
    hiddenyes="";
    hiddenno=" checked=\"checked\"";
  }
  String safemodeyes;
  String safemodeno;
  if (safemode==1){
    safemodeyes=" checked=\"checked\"";
    safemodeno="";
  }
  else {
    safemodeyes="";
    safemodeno=" checked=\"checked\"";
  }
  server.send(200, "text/html", 
  String()+
  F(
  "<!DOCTYPE HTML>"
  "<html>"
  "<head>"
  "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"
  "<title>ESP-RFID-Tool Settings</title>"
  "<style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:900px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}h1{color:#2c3e50;margin-bottom:25px;font-size:28px;font-weight:600}h2{color:#34495e;margin:25px 0 15px;font-size:20px;font-weight:500;padding-bottom:10px;border-bottom:2px solid #e9ecef}.form-group{margin:20px 0}.form-group label{display:block;margin-bottom:8px;font-weight:500;color:#495057;font-size:14px}.form-group small{display:block;color:#6c757d;font-size:13px;margin-top:5px;margin-bottom:10px}input[type=\"text\"],input[type=\"password\"],input[type=\"number\"],select{width:100%;max-width:400px;padding:10px 12px;border:1px solid #ced4da;border-radius:6px;font-size:15px;font-family:inherit;transition:border-color 0.3s,box-shadow 0.3s}input[type=\"text\"]:focus,input[type=\"password\"]:focus,input[type=\"number\"]:focus,select:focus{outline:none;border-color:#007bff;box-shadow:0 0 0 3px rgba(0,123,255,0.1)}input[type=\"radio\"]{margin-right:8px;margin-left:0;width:18px;height:18px;cursor:pointer}.radio-group{margin:10px 0}.radio-group label{display:inline;font-weight:400;margin-left:5px;cursor:pointer}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}input[type=\"submit\"]{background:#28a745;color:#fff;padding:12px 30px;border:none;border-radius:6px;font-size:16px;font-weight:500;cursor:pointer;transition:all 0.3s;font-family:inherit}input[type=\"submit\"]:hover{background:#218838;transform:translateY(-1px);box-shadow:0 4px 8px rgba(40,167,69,0.3)}hr{margin:30px 0;border:none;border-top:1px solid #e9ecef}</style>"
  "</head>"
  "<body>"
  "<div class=\"container\">"
  "<a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a>"
  "<h1>ESP-RFID-Tool Settings</h1>"
  "<a href=\"/restoredefaults\" class=\"btn btn-danger\">Restore Default Configuration</a>"
  "<hr>"
  "<FORM action=\"/settings\"  id=\"configuration\" method=\"post\">"
  "<h2>WiFi Configuration</h2>"
  "<div class=\"form-group\">"
  "<label>Network Type</label>"
  "<div class=\"radio-group\">"
  )+
  F("<label><INPUT type=\"radio\" name=\"accesspointmode\" value=\"1\"")+accesspointmodeyes+F("> Access Point Mode</label><br>"
  "<label><INPUT type=\"radio\" name=\"accesspointmode\" value=\"0\"")+accesspointmodeno+F("> Join Existing Network</label>"
  "</div></div>"
  "<div class=\"form-group\">"
  "<label>Hidden</label>"
  "<div class=\"radio-group\">"
  "<label><INPUT type=\"radio\" name=\"hidden\" value=\"1\"")+hiddenyes+F("> Yes</label><br>"
  "<label><INPUT type=\"radio\" name=\"hidden\" value=\"0\"")+hiddenno+F("> No</label>"
  "</div></div>"
  "<div class=\"form-group\">"
  "<label>SSID</label>"
  "<input type=\"text\" name=\"ssid\" value=\"")+ssid+F("\" maxlength=\"31\">"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Password</label>"
  "<input type=\"password\" name=\"password\" value=\"")+password+F("\" maxlength=\"64\">"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Channel</label>"
  "<select name=\"channel\" form=\"configuration\"><option value=\"")+channel+"\" selected>"+channel+F("</option><option value=\"1\">1</option><option value=\"2\">2</option><option value=\"3\">3</option><option value=\"4\">4</option><option value=\"5\">5</option><option value=\"6\">6</option><option value=\"7\">7</option><option value=\"8\">8</option><option value=\"9\">9</option><option value=\"10\">10</option><option value=\"11\">11</option><option value=\"12\">12</option><option value=\"13\">13</option><option value=\"14\">14</option></select>"
  "</div>"
  "<div class=\"form-group\">"
  "<label>IP Address</label>"
  "<input type=\"text\" name=\"local_IPstr\" value=\"")+local_IPstr+F("\" maxlength=\"16\">"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Gateway</label>"
  "<input type=\"text\" name=\"gatewaystr\" value=\"")+gatewaystr+F("\" maxlength=\"16\">"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Subnet</label>"
  "<input type=\"text\" name=\"subnetstr\" value=\"")+subnetstr+F("\" maxlength=\"16\">"
  "</div>"
  "<hr>"
  "<h2>Web Interface Administration Settings</h2>"
  "<div class=\"form-group\">"
  "<label>Username</label>"
  "<input type=\"text\" name=\"update_username\" value=\"")+update_username+F("\" maxlength=\"31\">"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Password</label>"
  "<input type=\"password\" name=\"update_password\" value=\"")+update_password+F("\" maxlength=\"64\">"
  "</div>"
  "<hr>"
  "<h2>FTP Server Settings</h2>"
  "<div class=\"form-group\">"
  "<small>Changes require a reboot.</small>"
  "<div class=\"radio-group\">"
  "<label><INPUT type=\"radio\" name=\"ftpenabled\" value=\"1\"")+ftpenabledyes+F("> Enabled</label><br>"
  "<label><INPUT type=\"radio\" name=\"ftpenabled\" value=\"0\"")+ftpenabledno+F("> Disabled</label>"
  "</div></div>"
  "<div class=\"form-group\">"
  "<label>FTP Username</label>"
  "<input type=\"text\" name=\"ftp_username\" value=\"")+ftp_username+F("\" maxlength=\"31\">"
  "</div>"
  "<div class=\"form-group\">"
  "<label>FTP Password</label>"
  "<input type=\"password\" name=\"ftp_password\" value=\"")+ftp_password+F("\" maxlength=\"64\">"
  "</div>"
  "<hr>"
  "<h2>Power LED</h2>"
  "<div class=\"form-group\">"
  "<small>Changes require a reboot.</small>"
  "<div class=\"radio-group\">"
  "<label><INPUT type=\"radio\" name=\"ledenabled\" value=\"1\"")+ledenabledyes+F("> Enabled</label><br>"
  "<label><INPUT type=\"radio\" name=\"ledenabled\" value=\"0\"")+ledenabledno+F("> Disabled</label>"
  "</div></div>"
  "<hr>"
  "<h2>RFID Capture Log</h2>"
  "<div class=\"form-group\">"
  "<label>File Name</label>"
  "<small>Useful to change this value to differentiate between facilities during various security assessments.</small>"
  "<input type=\"text\" name=\"logname\" value=\"")+logname+F("\" maxlength=\"30\">"
  "</div>"
  "<hr>"
  "<h2>Experimental Settings</h2>"
  "<div class=\"form-group\">"
  "<small>Changes require a reboot.</small>"
  "<small>Default Buffer Length is 256 bits with an allowed range of 52-4096 bits. Default Experimental TX mode timing is 40us Wiegand Data Pulse Width and a 2ms Wiegand Data Interval with an allowed range of 0-1000. Changing these settings may result in unstable performance.</small>"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Wiegand RX Buffer Length</label>"
  "<input type=\"number\" name=\"bufferlength\" value=\"")+bufferlength+F("\" min=\"52\" max=\"4096\"> <small>bit(s)</small>"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Wiegand RX Packet Length</label>"
  "<input type=\"number\" name=\"rxpacketgap\" value=\"")+rxpacketgap+F("\" min=\"1\" max=\"4096\"> <small>millisecond(s)</small>"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Experimental TX Wiegand Data Pulse Width</label>"
  "<input type=\"number\" name=\"txdelayus\" value=\"")+txdelayus+F("\" min=\"0\" max=\"1000\"> <small>microsecond(s)</small>"
  "</div>"
  "<div class=\"form-group\">"
  "<label>Experimental TX Wiegand Data Interval</label>"
  "<input type=\"number\" name=\"txdelayms\" value=\"")+txdelayms+F("\" min=\"0\" max=\"1000\"> <small>millisecond(s)</small>"
  "</div>"
  "<hr>"
  "<h2>Safe Mode</h2>"
  "<div class=\"form-group\">"
  "<small>Enable to reboot the device after every capture. Disable to avoid missing quick consecutive captures such as keypad entries.</small>"
  "<div class=\"radio-group\">"
  "<label><INPUT type=\"radio\" name=\"safemode\" value=\"1\"")+safemodeyes+F("> Enabled</label><br>"
  "<label><INPUT type=\"radio\" name=\"safemode\" value=\"0\"")+safemodeno+F("> Disabled</label>"
  "</div></div>"
  "<hr>"
  "<INPUT type=\"radio\" name=\"SETTINGS\" value=\"1\" hidden=\"1\" checked=\"checked\">"
  "<INPUT type=\"submit\" value=\"Apply Settings\">"
  "</FORM>"
  "<br><br><a href=\"/reboot\" class=\"btn btn-secondary\">Reboot Device</a>"
  "</div>"
  "</body>"
  "</html>"
  )
  );
}

void handleSettings()
{
  if (server.hasArg("SETTINGS")) {
    handleSubmitSettings();
  }
  else {
    settingsPage();
  }
}

void returnFail(String msg)
{
  server.sendHeader("Connection", "close");
  server.sendHeader("Access-Control-Allow-Origin", "*");
  server.send(500, "text/plain", msg + "\r\n");
}

void handleSubmitSettings()
{
  String SETTINGSvalue;

  if (!server.hasArg("SETTINGS")) return returnFail("BAD ARGS");
  
  SETTINGSvalue = server.arg("SETTINGS");
  accesspointmode = server.arg("accesspointmode").toInt();
  server.arg("ssid").toCharArray(ssid, 32);
  server.arg("password").toCharArray(password, 64);
  channel = server.arg("channel").toInt();
  hidden = server.arg("hidden").toInt();
  server.arg("local_IPstr").toCharArray(local_IPstr, 16);
  server.arg("gatewaystr").toCharArray(gatewaystr, 16);
  server.arg("subnetstr").toCharArray(subnetstr, 16);
  server.arg("update_username").toCharArray(update_username, 32);
  server.arg("update_password").toCharArray(update_password, 64);
  server.arg("ftp_username").toCharArray(ftp_username, 32);
  server.arg("ftp_password").toCharArray(ftp_password, 64);
  ftpenabled = server.arg("ftpenabled").toInt();
  ledenabled = server.arg("ledenabled").toInt();
  server.arg("logname").toCharArray(logname, 31);
  bufferlength = server.arg("bufferlength").toInt();
  rxpacketgap = server.arg("rxpacketgap").toInt();
  txdelayus = server.arg("txdelayus").toInt();
  txdelayms = server.arg("txdelayms").toInt();
  safemode = server.arg("safemode").toInt();
  
  if (SETTINGSvalue == "1") {
    saveConfig();
    server.send(200, "text/html", F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:800px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}.info-section{background:#d4edda;border-left:4px solid #28a745;padding:15px;margin:20px 0;border-radius:4px;color:#155724}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/reboot\" class=\"btn btn-primary\">Reboot Device</a><div class=\"info-section\"><p><strong>Settings have been saved.</strong></p><p>Some setting may require manually rebooting before taking effect. If network configuration has changed then be sure to connect to the new network first in order to access the web interface.</p></div></div></body></html>"));
    delay(50);
    loadConfig();
  }
  else if (SETTINGSvalue == "0") {
    settingsPage();
  }
  else {
    returnFail("Bad SETTINGS value");
  }
}

bool loadDefaults() {
  StaticJsonDocument<500> json;
  json["version"] = version;
  json["accesspointmode"] = "1";
  json["ssid"] = "ESP-RFID-Tool";
  json["password"] = "";
  json["channel"] = "6";
  json["hidden"] = "0";
  json["local_IP"] = "192.168.1.1";
  json["gateway"] = "192.168.1.1";
  json["subnet"] = "255.255.255.0";
  json["update_username"] = "admin";
  json["update_password"] = "rfidtool";
  json["ftp_username"] = "ftp-admin";
  json["ftp_password"] = "rfidtool";
  json["ftpenabled"] = "0";
  json["ledenabled"] = "1";
  json["logname"] = "log.txt";
  json["bufferlength"] = "256";
  json["rxpacketgap"] = "15";
  json["txdelayus"] = "40";
  json["txdelayms"] = "2";
  json["safemode"] = "0";
  File configFile = SPIFFS.open("/esprfidtool.json", "w");
  serializeJson(json, configFile);
  configFile.close();
  json.clear();
  loadConfig();
  return true;
}

bool loadConfig() {
  File configFile = SPIFFS.open("/esprfidtool.json", "r");
  if (!configFile) {
    delay(3500);
    loadDefaults();
  }

  size_t size = configFile.size();

  std::unique_ptr<char[]> buf(new char[size]);
  configFile.readBytes(buf.get(), size);
  StaticJsonDocument<500> json;
  deserializeJson(json, buf.get());
  
  if (!json["version"]) {
    delay(3500);
    loadDefaults();
    ESP.restart();
  }

  //Resets config to factory defaults on an update.
  if (json["version"]!=version) {
    delay(3500);
    loadDefaults();
    ESP.restart();
  }

  strcpy(ssid, (const char*)json["ssid"]);
  strcpy(password, (const char*)json["password"]);
  channel = json["channel"];
  hidden = json["hidden"];
  accesspointmode = json["accesspointmode"];
  strcpy(local_IPstr, (const char*)json["local_IP"]);
  strcpy(gatewaystr, (const char*)json["gateway"]);
  strcpy(subnetstr, (const char*)json["subnet"]);

  strcpy(update_username, (const char*)json["update_username"]);
  strcpy(update_password, (const char*)json["update_password"]);

  strcpy(ftp_username, (const char*)json["ftp_username"]);
  strcpy(ftp_password, (const char*)json["ftp_password"]);
  ftpenabled = json["ftpenabled"];
  ledenabled = json["ledenabled"];
  strcpy(logname, (const char*)json["logname"]);
  bufferlength = json["bufferlength"];
  rxpacketgap = json["rxpacketgap"];
  txdelayus = json["txdelayus"];
  txdelayms = json["txdelayms"];
  safemode = json["safemode"];
 
  IPAddress local_IP;
  local_IP.fromString(local_IPstr);
  IPAddress gateway;
  gateway.fromString(gatewaystr);
  IPAddress subnet;
  subnet.fromString(subnetstr);

  WiFi.persistent(false);

  if (accesspointmode == 1) {
    WiFi.disconnect(true);
    WiFi.mode(WIFI_AP);
    WiFi.softAP(ssid, password, channel, hidden);
    WiFi.softAPConfig(local_IP, gateway, subnet);
  }
// or Join existing network
  else if (accesspointmode != 1) {
    WiFi.disconnect(true);
    WiFi.mode(WIFI_STA);
    WiFi.config(local_IP, gateway, subnet);
    WiFi.begin(ssid, password);
    WiFi.reconnect();
  }
  configFile.close();
  json.clear();
  return true;
}

bool saveConfig() {
  StaticJsonDocument<500> json;
  json["version"] = version;
  json["accesspointmode"] = accesspointmode;
  json["ssid"] = ssid;
  json["password"] = password;
  json["channel"] = channel;
  json["hidden"] = hidden;
  json["local_IP"] = local_IPstr;
  json["gateway"] = gatewaystr;
  json["subnet"] = subnetstr;
  json["update_username"] = update_username;
  json["update_password"] = update_password;
  json["ftp_username"] = ftp_username;
  json["ftp_password"] = ftp_password;
  json["ftpenabled"] = ftpenabled;
  json["ledenabled"] = ledenabled;
  json["logname"] = logname;
  json["bufferlength"] = bufferlength;
  json["rxpacketgap"] = rxpacketgap;
  json["txdelayus"] = txdelayus;
  json["txdelayms"] = txdelayms;
  json["safemode"] = safemode;

  File configFile = SPIFFS.open("/esprfidtool.json", "w");
  serializeJson(json, configFile);
  configFile.close();
  json.clear();
  return true;
}

File fsUploadFile;
String webString;

void ListLogs(){
  String directory;
  directory="/";
  FSInfo fs_info;
  SPIFFS.info(fs_info);
  String total;
  total=fs_info.totalBytes;
  String used;
  used=fs_info.usedBytes;
  String freespace;
  freespace=fs_info.totalBytes-fs_info.usedBytes;
  Dir dir = SPIFFS.openDir(directory);
  String FileList = String()+F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:1000px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#f8f9fa;border-left:4px solid #007bff;padding:15px;margin:20px 0;border-radius:4px}.btn{display:inline-block;padding:8px 16px;margin:4px;text-decoration:none;border-radius:4px;font-size:14px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268}table{width:100%;border-collapse:collapse;margin:20px 0}th,td{padding:12px;text-align:left;border-bottom:1px solid #dee2e6}th{background:#f8f9fa;font-weight:600;color:#495057}tr:hover{background:#f8f9fa}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><div class=\"info-section\"><p><strong>File System Info (Bytes)</strong></p><p>Total: ")+total+F(" | Free: ")+freespace+F(" | Used: ")+used+F("</p><p><small>NOTE: Larger log files will need to be downloaded instead of viewed from the browser.</small></p></div><table><tr><th>Display File Contents</th><th>Size in Bytes</th><th>Download File</th><th>Delete File</th></tr>");
  while (dir.next()) {
    String FileName = dir.fileName();
    File f = dir.openFile("r");
    FileList += " ";
    if((!FileName.startsWith("/payloads/"))&&(!FileName.startsWith("/esploit.json"))&&(!FileName.startsWith("/esportal.json"))&&(!FileName.startsWith("/esprfidtool.json"))&&(!FileName.startsWith("/config.json"))) FileList += "<tr><td><a href=\"/viewlog?payload="+FileName+"\" style=\"color:#007bff;text-decoration:none\">"+FileName+"</a></td>"+"<td>"+f.size()+"</td><td><a href=\""+FileName+"\" class=\"btn btn-primary\">Download</a></td><td><a href=\"/deletelog?payload="+FileName+"\" class=\"btn btn-danger\">Delete</a></td></tr>";
    f.close();
  }
  FileList += "</table></div></body></html>";
  server.send(200, "text/html", FileList);
}

bool RawFile(String rawfile) {
  if (SPIFFS.exists(rawfile)) {
    if(!server.authenticate(update_username, update_password)){
      server.requestAuthentication();}
    File file = SPIFFS.open(rawfile, "r");
    size_t sent = server.streamFile(file, "application/octet-stream");
    file.close();
    return true;
  }
  return false;
}

void ViewLog(){
  webString="";
  String payload;
  String ShowPL;
  payload += server.arg(0);
  File f = SPIFFS.open(payload, "r");
  String webString = f.readString();
  f.close();
  ShowPL = String()+F(
    "<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:1200px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}h1{color:#2c3e50;margin-bottom:25px;font-size:28px;font-weight:600}h2{color:#34495e;margin:25px 0 15px;font-size:20px;font-weight:500;padding-bottom:10px;border-bottom:2px solid #e9ecef}.form-group{margin:20px 0}.form-group label{display:block;margin-bottom:8px;font-weight:500;color:#495057;font-size:15px}.form-group small{display:block;color:#6c757d;font-size:13px;margin-top:5px;margin-bottom:10px}input[type=\"text\"],input[type=\"password\"],input[type=\"number\"],select{width:100%;max-width:600px;padding:10px 12px;border:1px solid #ced4da;border-radius:6px;font-size:15px;font-family:inherit;transition:border-color 0.3s,box-shadow 0.3s}input[type=\"text\"]:focus,input[type=\"password\"]:focus,input[type=\"number\"]:focus,select:focus{outline:none;border-color:#007bff;box-shadow:0 0 0 3px rgba(0,123,255,0.1)}input[type=\"submit\"]{background:#28a745;color:#fff;padding:12px 30px;border:none;border-radius:6px;font-size:16px;font-weight:500;cursor:pointer;transition:all 0.3s;font-family:inherit;margin-top:10px}input[type=\"submit\"]:hover{background:#218838;transform:translateY(-1px);box-shadow:0 4px 8px rgba(40,167,69,0.3)}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}pre{background:#f8f9fa;border:1px solid #e9ecef;border-radius:6px;padding:15px;overflow-x:auto;font-family:monospace;font-size:13px;line-height:1.5;margin:20px 0}hr{margin:30px 0;border:none;border-top:1px solid #e9ecef}</style></head><body><div class=\"container\"><h1>View Log File</h1><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/logs\" class=\"btn btn-primary\">List Exfiltrated Data</a> <a href=\"/experimental\" class=\"btn btn-primary\">Experimental TX Mode</a> <a href=\"/data-convert\" class=\"btn btn-primary\">Data Conversion Tools</a><hr><h2>Transmit Binary Data</h2><FORM action=\"/api/tx/bin\" id=\"api_tx\" method=\"get\" target=\"_blank\">"
      "<div class=\"form-group\">"
      "<label>Binary Data</label>"
      "<small>Use commas to separate the binary for transmitting multiple packets (useful for sending multiple keypresses for imitating keypads)</small>"
      "<INPUT form=\"api_tx\" type=\"text\" name=\"binary\" value=\"\" pattern=\"[01,]{1,}\" required title=\"Allowed characters (0,1, comma), must not be empty\" minlength=\"1\">"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Pulse Width</label>"
      "<INPUT form=\"api_tx\" type=\"number\" name=\"pulsewidth\" value=\"40\" min=\"0\" style=\"max-width:200px\"> <small>us</small>"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Data Interval</label>"
      "<INPUT form=\"api_tx\" type=\"number\" name=\"interval\" value=\"2000\" min=\"0\" style=\"max-width:200px\"> <small>us</small>"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Delay Between Packets</label>"
      "<INPUT form=\"api_tx\" type=\"number\" name=\"wait\" value=\"100000\" min=\"0\" style=\"max-width:200px\"> <small>us</small>"
      "</div>"
      "<INPUT form=\"api_tx\" type=\"hidden\" name=\"prettify\" id=\"prettify\" value=\"1\">"
      "<INPUT form=\"api_tx\" type=\"submit\" value=\"Transmit\">"
    "</FORM>"
    "<hr>"
    "<a href=\"")+payload+F("\" class=\"btn btn-primary\">Download File</a> <a href=\"/deletelog?payload=")+payload+F("\" class=\"btn btn-danger\">Delete File</a>"
    "<pre>")
    +payload+
    F("\n"
    "Note: Preambles shown are only a guess based on card length and may not be accurate for every card format.\n"
    "-----\n")
    +webString+
    F("</pre></div></body></html>")
    ;
  webString="";
  server.send(200, "text/html", ShowPL);
}

// Start Networking
void setup() {
  Serial.begin(9600);
  Serial.println(F("....."));
  Serial.println(String()+F("ESP-RFID-Tool v")+version);
  //SPIFFS.format();
  
  SPIFFS.begin();
  
 //loadDefaults(); //uncomment to restore default settings if double reset fails for some reason

//Jump RESTORE_DEFAULTS_PIN to GND while powering on device to reset the device to factory defaults
  pinMode(RESTORE_DEFAULTS_PIN, INPUT_PULLUP);
  jumperState = digitalRead(RESTORE_DEFAULTS_PIN);
  if (jumperState == LOW) {
    Serial.println(String()+F("Pin ")+RESTORE_DEFAULTS_PIN+F("Grounded"));
    Serial.println(F("Loading default config..."));
    loadDefaults();
  }
  
  loadConfig();

  if(!wg.begin(DATA0,DATA1,bufferlength,rxpacketgap)) {       
    Serial.println(F("Could not begin Wiegand logging,"));            
    Serial.println(F("Out of memory!"));
  }

//Set up Web Pages
  server.on("/",[]() {
    FSInfo fs_info;
    SPIFFS.info(fs_info);
    String total = String(fs_info.totalBytes);
    String used = String(fs_info.usedBytes);
    String freespace = String(fs_info.totalBytes-fs_info.usedBytes);
    server.send(200, "text/html", String()+F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:800px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}h1{color:#2c3e50;margin-bottom:20px;font-size:28px;font-weight:600}h2{color:#34495e;margin:20px 0 15px;font-size:20px;font-weight:500}.info-section{background:#f8f9fa;border-left:4px solid #007bff;padding:15px;margin:20px 0;border-radius:4px}.info-section p{margin:5px 0}.info-section strong{color:#007bff}.button-group{margin:20px 0}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}.footer{text-align:center;color:#6c757d;font-size:14px;margin-top:30px;padding-top:20px;border-top:1px solid #e9ecef}.footer a{color:#007bff;text-decoration:none}.footer a:hover{text-decoration:underline}</style></head><body><div class=\"container\"><h1>ESP-RFID-Tool v")+version+F("</h1><div class=\"info-section\"><p><strong>by Corey Harding</strong></p><p><a href=\"http://www.RFID-Tool.com\" target=\"_blank\">www.RFID-Tool.com</a></p><p><a href=\"http://www.LegacySecurityGroup.com\" target=\"_blank\">www.LegacySecurityGroup.com</a> / <a href=\"http://www.Exploit.Agency\" target=\"_blank\">www.Exploit.Agency</a></p></div><div class=\"info-section\"><p><strong>File System Info (Bytes)</strong></p><p>Total: ")+total+F(" | Free: ")+freespace+F(" | Used: ")+used+F("</p></div><div class=\"button-group\"><a href=\"/logs\" class=\"btn btn-primary\">List Exfiltrated Data</a><a href=\"/cardbeep\" class=\"btn btn-primary\">Beep and Show When Card Recorded</a><a href=\"/experimental\" class=\"btn btn-primary\">Experimental TX Mode</a><a href=\"/data-convert\" class=\"btn btn-primary\">Data Conversion Tools</a><a href=\"/settings\" class=\"btn btn-primary\">Configure Settings</a><a href=\"/format\" class=\"btn btn-danger\">Format File System</a><a href=\"/firmware\" class=\"btn btn-primary\">Upgrade Firmware</a><a href=\"/api/help\" class=\"btn btn-primary\">API Info</a><a href=\"/help\" class=\"btn btn-primary\">Help</a></div></div></body></html>"));
  });

  server.onNotFound([]() {
    if (!RawFile(server.uri()))
      server.send(404, "text/plain", F("Error 404 File Not Found"));
  });
  server.on("/settings", handleSettings);

  server.on("/firmware", [](){
    server.send(200, "text/html", String()+F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px;height:100vh}.container{max-width:900px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}.info-section{margin:20px 0;padding:15px;background:#f8f9fa;border-radius:4px}iframe{border:none;width:100%;height:600px;border-radius:6px;margin-top:20px}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><div class=\"info-section\"><p><strong>Firmware Upgrade Instructions:</strong></p><p>1. Open Arduino IDE</p><p>2. Pull down \"Sketch\" Menu then select \"Export Compiled Binary\"</p><p>3. On this page click \"Browse\", select the binary you exported earlier, then click \"Update\"</p><p>4. You may need to manually reboot the device to reconnect</p></div><iframe src=\"http://")+local_IPstr+F(":1337/update\"></iframe></div></body></html>"));
  });

  server.on("/restoredefaults", [](){
    server.send(200, "text/html", F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.warning-section{background:#fff3cd;border-left:4px solid #ffc107;padding:20px;margin:20px 0;border-radius:4px;color:#856404}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><div class=\"warning-section\"><p><strong>Restore Default Configuration</strong></p><p>This will restore the device to the default configuration.</p><p><strong>Are you sure?</strong></p></div><a href=\"/restoredefaults/yes\" class=\"btn btn-danger\">YES</a><a href=\"/\" class=\"btn btn-secondary\">NO</a></div></body></html>"));
  });

  server.on("/restoredefaults/yes", [](){
    if(!server.authenticate(update_username, update_password))
      return server.requestAuthentication();
    server.send(200, "text/html", F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#d1ecf1;border-left:4px solid #0c5460;padding:20px;margin:20px 0;border-radius:4px;color:#0c5460}.info-section p{margin:10px 0}.info-section strong{display:block;margin-bottom:5px}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><div class=\"info-section\"><p><strong>Network</strong></p><p>SSID: <strong>ESP-RFID-Tool</strong></p><p><strong>Administration</strong></p><p>USER: <strong>admin</strong></p><p>PASS: <strong>rfidtool</strong></p></div></div></body></html>"));
    delay(50);
    loadDefaults();
    ESP.restart();
  });

  server.on("/deletelog", [](){
    String deletelog;
    deletelog += server.arg(0);
    server.send(200, "text/html", String()+F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.warning-section{background:#f8d7da;border-left:4px solid #dc3545;padding:20px;margin:20px 0;border-radius:4px;color:#721c24}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><div class=\"warning-section\"><p><strong>Delete File</strong></p><p>This will delete the file: ")+deletelog+F("</p><p><strong>Are you sure?</strong></p></div><a href=\"/deletelog/yes?payload=")+deletelog+F("\" class=\"btn btn-danger\">YES</a><a href=\"/\" class=\"btn btn-secondary\">NO</a></div></body></html>"));
  });

  server.on("/viewlog", ViewLog);

  server.on("/deletelog/yes", [](){
    if(!server.authenticate(update_username, update_password))
      return server.requestAuthentication();
    String deletelog;
    deletelog += server.arg(0);
    if (!deletelog.startsWith("/payloads/")) server.send(200, "text/html", String()+F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#d1ecf1;border-left:4px solid #17a2b8;padding:20px;margin:20px 0;border-radius:4px;color:#0c5460}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/logs\" class=\"btn btn-primary\">List Exfiltrated Data</a><div class=\"info-section\"><p><strong>Deleting file:</strong> ")+deletelog+F("</p></div></div></body></html>"));
    delay(50);
    SPIFFS.remove(deletelog);
  });

  server.on("/cardbeep", [](){
    server.send(200, "text/html", String()+F(
      "<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><title>Card Beeper</title><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:1000px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}h1{color:#2c3e50;margin-bottom:25px;font-size:28px;font-weight:600}#cards p{background:#f8f9fa;border-left:4px solid #007bff;padding:15px;margin:10px 0;border-radius:4px;font-family:monospace;font-size:13px}</style></head>\n"
      "<body><div class=\"container\"><h1>Card Beeper</h1><div id=\"cards\"></div></div>\n"
      "<script>\n"
      "function beep() {\nvar snd = new Audio(\"data:audio/wav;base64,//uQRAAAAWMSLwUIYAAsYkXgoQwAEaYLWfkWgAI0wWs/ItAAAGDgYtAgAyN+QWaAAihwMWm4G8QQRDiMcCBcH3Cc+CDv/7xA4Tvh9Rz/y8QADBwMWgQAZG/ILNAARQ4GLTcDeIIIhxGOBAuD7hOfBB3/94gcJ3w+o5/5eIAIAAAVwWgQAVQ2ORaIQwEMAJiDg95G4nQL7mQVWI6GwRcfsZAcsKkJvxgxEjzFUgfHoSQ9Qq7KNwqHwuB13MA4a1q/DmBrHgPcmjiGoh//EwC5nGPEmS4RcfkVKOhJf+WOgoxJclFz3kgn//dBA+ya1GhurNn8zb//9NNutNuhz31f////9vt///z+IdAEAAAK4LQIAKobHItEIYCGAExBwe8jcToF9zIKrEdDYIuP2MgOWFSE34wYiR5iqQPj0JIeoVdlG4VD4XA67mAcNa1fhzA1jwHuTRxDUQ//iYBczjHiTJcIuPyKlHQkv/LHQUYkuSi57yQT//uggfZNajQ3Vmz+Zt//+mm3Wm3Q576v////+32///5/EOgAAADVghQAAAAA//uQZAUAB1WI0PZugAAAAAoQwAAAEk3nRd2qAAAAACiDgAAAAAAABCqEEQRLCgwpBGMlJkIz8jKhGvj4k6jzRnqasNKIeoh5gI7BJaC1A1AoNBjJgbyApVS4IDlZgDU5WUAxEKDNmmALHzZp0Fkz1FMTmGFl1FMEyodIavcCAUHDWrKAIA4aa2oCgILEBupZgHvAhEBcZ6joQBxS76AgccrFlczBvKLC0QI2cBoCFvfTDAo7eoOQInqDPBtvrDEZBNYN5xwNwxQRfw8ZQ5wQVLvO8OYU+mHvFLlDh05Mdg7BT6YrRPpCBznMB2r//xKJjyyOh+cImr2/4doscwD6neZjuZR4AgAABYAAAABy1xcdQtxYBYYZdifkUDgzzXaXn98Z0oi9ILU5mBjFANmRwlVJ3/6jYDAmxaiDG3/6xjQQCCKkRb/6kg/wW+kSJ5//rLobkLSiKmqP/0ikJuDaSaSf/6JiLYLEYnW/+kXg1WRVJL/9EmQ1YZIsv/6Qzwy5qk7/+tEU0nkls3/zIUMPKNX/6yZLf+kFgAfgGyLFAUwY//uQZAUABcd5UiNPVXAAAApAAAAAE0VZQKw9ISAAACgAAAAAVQIygIElVrFkBS+Jhi+EAuu+lKAkYUEIsmEAEoMeDmCETMvfSHTGkF5RWH7kz/ESHWPAq/kcCRhqBtMdokPdM7vil7RG98A2sc7zO6ZvTdM7pmOUAZTnJW+NXxqmd41dqJ6mLTXxrPpnV8avaIf5SvL7pndPvPpndJR9Kuu8fePvuiuhorgWjp7Mf/PRjxcFCPDkW31srioCExivv9lcwKEaHsf/7ow2Fl1T/9RkXgEhYElAoCLFtMArxwivDJJ+bR1HTKJdlEoTELCIqgEwVGSQ+hIm0NbK8WXcTEI0UPoa2NbG4y2K00JEWbZavJXkYaqo9CRHS55FcZTjKEk3NKoCYUnSQ0rWxrZbFKbKIhOKPZe1cJKzZSaQrIyULHDZmV5K4xySsDRKWOruanGtjLJXFEmwaIbDLX0hIPBUQPVFVkQkDoUNfSoDgQGKPekoxeGzA4DUvnn4bxzcZrtJyipKfPNy5w+9lnXwgqsiyHNeSVpemw4bWb9psYeq//uQZBoABQt4yMVxYAIAAAkQoAAAHvYpL5m6AAgAACXDAAAAD59jblTirQe9upFsmZbpMudy7Lz1X1DYsxOOSWpfPqNX2WqktK0DMvuGwlbNj44TleLPQ+Gsfb+GOWOKJoIrWb3cIMeeON6lz2umTqMXV8Mj30yWPpjoSa9ujK8SyeJP5y5mOW1D6hvLepeveEAEDo0mgCRClOEgANv3B9a6fikgUSu/DmAMATrGx7nng5p5iimPNZsfQLYB2sDLIkzRKZOHGAaUyDcpFBSLG9MCQALgAIgQs2YunOszLSAyQYPVC2YdGGeHD2dTdJk1pAHGAWDjnkcLKFymS3RQZTInzySoBwMG0QueC3gMsCEYxUqlrcxK6k1LQQcsmyYeQPdC2YfuGPASCBkcVMQQqpVJshui1tkXQJQV0OXGAZMXSOEEBRirXbVRQW7ugq7IM7rPWSZyDlM3IuNEkxzCOJ0ny2ThNkyRai1b6ev//3dzNGzNb//4uAvHT5sURcZCFcuKLhOFs8mLAAEAt4UWAAIABAAAAAB4qbHo0tIjVkUU//uQZAwABfSFz3ZqQAAAAAngwAAAE1HjMp2qAAAAACZDgAAAD5UkTE1UgZEUExqYynN1qZvqIOREEFmBcJQkwdxiFtw0qEOkGYfRDifBui9MQg4QAHAqWtAWHoCxu1Yf4VfWLPIM2mHDFsbQEVGwyqQoQcwnfHeIkNt9YnkiaS1oizycqJrx4KOQjahZxWbcZgztj2c49nKmkId44S71j0c8eV9yDK6uPRzx5X18eDvjvQ6yKo9ZSS6l//8elePK/Lf//IInrOF/FvDoADYAGBMGb7FtErm5MXMlmPAJQVgWta7Zx2go+8xJ0UiCb8LHHdftWyLJE0QIAIsI+UbXu67dZMjmgDGCGl1H+vpF4NSDckSIkk7Vd+sxEhBQMRU8j/12UIRhzSaUdQ+rQU5kGeFxm+hb1oh6pWWmv3uvmReDl0UnvtapVaIzo1jZbf/pD6ElLqSX+rUmOQNpJFa/r+sa4e/pBlAABoAAAAA3CUgShLdGIxsY7AUABPRrgCABdDuQ5GC7DqPQCgbbJUAoRSUj+NIEig0YfyWUho1VBBBA//uQZB4ABZx5zfMakeAAAAmwAAAAF5F3P0w9GtAAACfAAAAAwLhMDmAYWMgVEG1U0FIGCBgXBXAtfMH10000EEEEEECUBYln03TTTdNBDZopopYvrTTdNa325mImNg3TTPV9q3pmY0xoO6bv3r00y+IDGid/9aaaZTGMuj9mpu9Mpio1dXrr5HERTZSmqU36A3CumzN/9Robv/Xx4v9ijkSRSNLQhAWumap82WRSBUqXStV/YcS+XVLnSS+WLDroqArFkMEsAS+eWmrUzrO0oEmE40RlMZ5+ODIkAyKAGUwZ3mVKmcamcJnMW26MRPgUw6j+LkhyHGVGYjSUUKNpuJUQoOIAyDvEyG8S5yfK6dhZc0Tx1KI/gviKL6qvvFs1+bWtaz58uUNnryq6kt5RzOCkPWlVqVX2a/EEBUdU1KrXLf40GoiiFXK///qpoiDXrOgqDR38JB0bw7SoL+ZB9o1RCkQjQ2CBYZKd/+VJxZRRZlqSkKiws0WFxUyCwsKiMy7hUVFhIaCrNQsKkTIsLivwKKigsj8XYlwt/WKi2N4d//uQRCSAAjURNIHpMZBGYiaQPSYyAAABLAAAAAAAACWAAAAApUF/Mg+0aohSIRobBAsMlO//Kk4soosy1JSFRYWaLC4qZBYWFRGZdwqKiwkNBVmoWFSJkWFxX4FFRQWR+LsS4W/rFRb/////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////////VEFHAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAU291bmRib3kuZGUAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAMjAwNGh0dHA6Ly93d3cuc291bmRib3kuZGUAAAAAAAAAACU=\");\nsnd.play();\n}\n"
      "var cards=-1;\n"
      "function checkCards() {\n"
        "var xhttp = new XMLHttpRequest();\n"
        "xhttp.onreadystatechange = function() {\n"
          "if (this.readyState == 4) {\n"
            "try {\n"
              "if(this.status == 200) {\n"
                "if (this.responseText.indexOf(\"Log file not found\") > -1) {\n"
                  "cards = 0;\n"
                "}\n"
                "else {\n"
                  "var result = JSON.parse(this.responseText);\n"
                  "if(cards != result[\"CaptureCount\"]) {\n"
                    "if(cards != -1) {\n"
                      "beep();\n"
                      "var p = document.createElement(\"p\");\n"
                      "p.innerHTML = JSON.stringify(result[\"Captures\"][result[\"CaptureCount\"] - 1]);\n"
                      "document.getElementById(\"cards\").append(p);\n"
                    "}\n"
                    "cards = result[\"CaptureCount\"];\n"
                  "}\n"
                "}\n"
              "}\n"
            "} catch {}\n"
            "window.setTimeout(checkCards, 500);\n"
          "}\n"
        "}\n"
        "xhttp.open(\"GET\", \"/api/viewlog?logfile=log.txt\", true);\n"
        "xhttp.send();\n"
      "}\n"
      "checkCards();\n"
      "</script>\n</body>\n</html>\n"));
  });

  server.on("/format", [](){
    server.send(200, "text/html", F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.warning-section{background:#f8d7da;border-left:4px solid #dc3545;padding:20px;margin:20px 0;border-radius:4px;color:#721c24}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><div class=\"warning-section\"><p><strong>Format File System</strong></p><p>This will reformat the SPIFFS File System.</p><p><strong>Are you sure?</strong></p></div><a href=\"/format/yes\" class=\"btn btn-danger\">YES</a><a href=\"/\" class=\"btn btn-secondary\">NO</a></div></body></html>"));
  });

  server.on("/logs", ListLogs);

  server.on("/reboot", [](){
    if(!server.authenticate(update_username, update_password))
    return server.requestAuthentication();
    server.send(200, "text/html", F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#d1ecf1;border-left:4px solid #17a2b8;padding:20px;margin:20px 0;border-radius:4px;color:#0c5460}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><div class=\"info-section\"><p><strong>Rebooting Device...</strong></p></div></div></body></html>"));
    delay(50);
    ESP.restart();
  });
  
  server.on("/format/yes", [](){
    if(!server.authenticate(update_username, update_password))
      return server.requestAuthentication();
    server.send(200, "text/html", F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#d1ecf1;border-left:4px solid #17a2b8;padding:20px;margin:20px 0;border-radius:4px;color:#0c5460}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><div class=\"info-section\"><p><strong>Formatting file system</strong></p><p>This may take up to 90 seconds</p></div></div></body></html>"));
    delay(50);
//    Serial.print("Formatting file system...");
    SPIFFS.format();
//    Serial.println(" Success");
    saveConfig();
  });
  
  server.on("/help", []() {
    server.send_P(200, "text/html", HelpText);
  });
  
  server.on("/license", []() {
    server.send_P(200, "text/html", License);
  });

  server.on("/data-convert", [](){

    if (server.hasArg("bin2hexHTML")) {

      int bin2hexBUFFlen=(((server.arg("bin2hexHTML")).length())+1);
      char bin2hexCHAR[bin2hexBUFFlen];
      (server.arg("bin2hexHTML")).toCharArray(bin2hexCHAR,bin2hexBUFFlen);

      dataCONVERSION+=String()+F("Binary: ")+bin2hexCHAR+F("<br><br>");

      String hexTEMP="";

      int binCOUNT=(bin2hexBUFFlen-1);
      for (int currentBINpos=0; currentBINpos<binCOUNT; currentBINpos=currentBINpos+4) {
        char hexCHAR[2];
        char tempNIBBLE[5];
        strncpy(tempNIBBLE, &bin2hexCHAR[currentBINpos], 4);
        tempNIBBLE[4]='\0';
        sprintf(hexCHAR, "%X", (strtol(tempNIBBLE, NULL, 2)));
        hexTEMP+=hexCHAR;
      }

      dataCONVERSION+=String()+F("Hexadecimal: ")+hexTEMP+F("<br><small>You may want to drop the leading zero(if there is one) and if your cloning software does not handle it for you.</small><br><br>");
      hexTEMP="";
      
      dataCONVERSION+=F("<br><br>");
      
      bin2hexBUFFlen=0;
    }

    if (server.hasArg("hex2binHTML")) {

      int hex2binBUFFlen=(((server.arg("hex2binHTML")).length())+1);
      char hex2binCHAR[hex2binBUFFlen];
      (server.arg("hex2binHTML")).toCharArray(hex2binCHAR,hex2binBUFFlen);

      dataCONVERSION+=String()+F("Hexadecimal: ")+hex2binCHAR+F("<br><br>");

      String binTEMP="";

      int charCOUNT=(hex2binBUFFlen-1);
      for (int currentHEXpos=0; currentHEXpos<charCOUNT; currentHEXpos++) {
        char binCHAR[5];
        char tempHEX[2];
        strncpy(tempHEX, &hex2binCHAR[currentHEXpos], 1);
        tempHEX[1]='\0';
        int decimal=(unsigned char)strtoul(tempHEX, NULL, 16);
        itoa(decimal,binCHAR,2);
        while (strlen(binCHAR) < 4) {
          char *dup;
          sprintf(binCHAR,"%s%s","0",(dup=strdup(binCHAR)));
          free(dup);
        }
        binTEMP+=binCHAR;
      }

      dataCONVERSION+=String()+F("Binary: ")+binTEMP+F("<br><br>");
      binTEMP="";
      
      dataCONVERSION+=F("<br><br>");
      
      hex2binBUFFlen=0;
    }
    
    if (server.hasArg("abaHTML")) {
      String abaHTML=(server.arg("abaHTML"));

      dataCONVERSION="Trying \"Forward\" Swipe<br>";
      dataCONVERSION+=("Forward Binary:"+abaHTML+"<br>");
      int abaStart=abaHTML.indexOf("11010");
      int abaEnd=(abaHTML.lastIndexOf("11111")+4);
      dataCONVERSION+=aba2str(abaHTML,abaStart,abaEnd,"\"Forward\" Swipe");
      
      dataCONVERSION+=" * Trying \"Reverse\" Swipe<br>";
      int abaBUFFlen=((abaHTML.length())+1);
      char abachar[abaBUFFlen];
      abaHTML.toCharArray(abachar,abaBUFFlen);
      abaHTML=String(strrev(abachar));
      dataCONVERSION+=("Reversed Binary:"+abaHTML+"<br>");
      abaStart=abaHTML.indexOf("11010");
      abaEnd=(abaHTML.lastIndexOf("11111")+4);
      dataCONVERSION+=aba2str(abaHTML,abaStart,abaEnd,"\"Reverse\" Swipe");
    
      //dataCONVERSION+=(String()+F(" * You can verify the data at the following URL:<br><a target=\"_blank\" href=\"https://www.legacysecuritygroup.com/aba-decode.php?binary=")+abaHTML+F("\">https://www.legacysecuritygroup.com/aba-decode.php?binary=")+abaHTML+F("</a>"));
      dataCONVERSION.replace("*", "<br><br>");
      dataCONVERSION.replace(":", ": ");

      abaHTML="";
      abaStart=0;
      abaEnd=0;
    }
    
    server.send(200, "text/html", String()+F(
      "<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:900px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}h1{color:#2c3e50;margin-bottom:25px;font-size:28px;font-weight:600}h2{color:#34495e;margin:25px 0 15px;font-size:20px;font-weight:500;padding-bottom:10px;border-bottom:2px solid #e9ecef}.form-group{margin:25px 0}.form-group label{display:block;margin-bottom:8px;font-weight:500;color:#495057;font-size:15px}.form-group small{display:block;color:#6c757d;font-size:13px;margin-top:5px;margin-bottom:10px}input[type=\"text\"],input[type=\"password\"],input[type=\"number\"],select{width:100%;max-width:600px;padding:10px 12px;border:1px solid #ced4da;border-radius:6px;font-size:15px;font-family:inherit;transition:border-color 0.3s,box-shadow 0.3s}input[type=\"text\"]:focus,input[type=\"password\"]:focus,input[type=\"number\"]:focus,select:focus{outline:none;border-color:#007bff;box-shadow:0 0 0 3px rgba(0,123,255,0.1)}input[type=\"submit\"]{background:#28a745;color:#fff;padding:12px 30px;border:none;border-radius:6px;font-size:16px;font-weight:500;cursor:pointer;transition:all 0.3s;font-family:inherit;margin-top:10px}input[type=\"submit\"]:hover{background:#218838;transform:translateY(-1px);box-shadow:0 4px 8px rgba(40,167,69,0.3)}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}.result-section{background:#f8f9fa;border-left:4px solid #007bff;padding:15px;margin:20px 0;border-radius:4px;white-space:pre-wrap;font-family:monospace;font-size:14px}hr{margin:30px 0;border:none;border-top:1px solid #e9ecef}</style></head><body><div class=\"container\"><h1>Data Conversion Tools</h1><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a>")
      +dataCONVERSION+
      F(
      "<hr>"
      "<h2>Convert ABA Binary Data to ASCII</h2>"
      "<FORM action=\"/data-convert\" id=\"aba2ascii\" method=\"post\">"
      "<div class=\"form-group\">"
      "<label>Binary Data</label>"
      "<INPUT form=\"aba2ascii\" type=\"text\" name=\"abaHTML\" value=\"\" pattern=\"[0-1]{1,}\" required title=\"Only 0's & 1's allowed, must not be empty\" minlength=\"1\">"
      "</div>"
      "<INPUT form=\"aba2ascii\" type=\"submit\" value=\"Convert\">"
      "</FORM>"
      "<hr>"
      "<h2>Convert Binary Data to Hexadecimal</h2>"
      "<FORM action=\"/data-convert\" id=\"bin2hex\" method=\"post\">"
      "<div class=\"form-group\">"
      "<label>Binary Data</label>"
      "<small>For use with card cloning, typically includes both the preamble and card data (binary before and after the space in log).</small>"
      "<INPUT form=\"bin2hex\" type=\"text\" name=\"bin2hexHTML\" value=\"\" pattern=\"[0-1]{1,}\" required title=\"Only 0's & 1's allowed, no spaces allowed, must not be empty\" minlength=\"1\">"
      "</div>"
      "<INPUT form=\"bin2hex\" type=\"submit\" value=\"Convert\">"
      "</FORM>"
      "<hr>"
      "<h2>Convert Hexadecimal Data to Binary</h2>"
      "<FORM action=\"/data-convert\" id=\"hex2bin\" method=\"post\">"
      "<div class=\"form-group\">"
      "<label>Hexadecimal Data</label>"
      "<small>In some situations you may want to add a leading zero to pad the output to come up with the correct number of bits.</small>"
      "<INPUT form=\"hex2bin\" type=\"text\" name=\"hex2binHTML\" value=\"\" pattern=\"[0-9a-fA-F]{1,}\" required title=\"Only characters 0-9 A-F a-f allowed, no spaces allowed, must not be empty\" minlength=\"1\">"
      "</div>"
      "<INPUT form=\"hex2bin\" type=\"submit\" value=\"Convert\">"
      "</FORM>"
      "</div></body></html>"
      )
    );
      
    dataCONVERSION="";
  });

  #include "api_server.h"

  server.on("/stoptx", [](){
    server.send(200, "text/html", F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.warning-section{background:#f8d7da;border-left:4px solid #dc3545;padding:20px;margin:20px 0;border-radius:4px;color:#721c24}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><div class=\"warning-section\"><p><strong>Stop Transmission</strong></p><p>This will kill any ongoing transmissions.</p><p><strong>Are you sure?</strong></p></div><a href=\"/stoptx/yes\" class=\"btn btn-danger\">YES</a><a href=\"/\" class=\"btn btn-secondary\">NO</a></div></body></html>"));
  });

  server.on("/stoptx/yes", [](){
    TXstatus=0;
    server.send(200, "text/html", F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:600px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#d4edda;border-left:4px solid #28a745;padding:20px;margin:20px 0;border-radius:4px;color:#155724}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/experimental\" class=\"btn btn-primary\">BACK TO EXPERIMENTAL TX MODE</a><div class=\"info-section\"><p><strong>All transmissions have been stopped.</strong></p></div></div></body></html>"));
  });

  server.on("/experimental", [](){
    String experimentalStatus="Awaiting Instructions";

    if (server.hasArg("pinHTML")||server.hasArg("bruteEND")) {
      pinHTML=server.arg("pinHTML");
      int pinBITS=server.arg("pinBITS").toInt();
      int pinHTMLDELAY=server.arg("pinHTMLDELAY").toInt();
      int bruteforcing;
      int brutePAD=(server.arg("bruteSTART").length());
      if (server.hasArg("bruteSTART")) {
        bruteforcing=1;
      }
      else {
        bruteforcing=0;
      }

      TXstatus=1;
      
      wg.pause();
      digitalWrite(DATA0, HIGH);
      pinMode(DATA0,OUTPUT);
      digitalWrite(DATA1, HIGH);
      pinMode(DATA1,OUTPUT);

      pinHTML.replace("F1","C");
      pinHTML.replace("F2","D");
      pinHTML.replace("F3","E");
      pinHTML.replace("F4","F");

      experimentalStatus=String()+"Transmitting "+pinBITS+"bit Wiegand Format PIN: "+pinHTML+" with a "+pinHTMLDELAY+"ms delay between \"keypresses\"";
      delay(50);
      
      int bruteSTART;
      int bruteEND;
      if (server.hasArg("bruteSTART")) {
        bruteSTART=server.arg("bruteSTART").toInt();
      }
      else {
        bruteSTART=0;
      }
      
      if (server.hasArg("bruteEND")) {
        bruteEND=server.arg("bruteEND").toInt();
      }
      else {
        bruteEND=0;
      }

      if (server.hasArg("bruteSTART")) {
        server.send(200, "text/html", String()+F("<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:800px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#d1ecf1;border-left:4px solid #17a2b8;padding:20px;margin:20px 0;border-radius:4px;color:#0c5460}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/experimental\" class=\"btn btn-primary\">BACK TO EXPERIMENTAL TX MODE</a><div class=\"info-section\"><p><strong>Brute forcing ")+pinBITS+F("bit Wiegand Format PIN</strong></p><p>From ")+(server.arg("bruteSTART"))+F(" to ")+(server.arg("bruteEND"))+F(" with a ")+pinHTMLDELAY+F("ms delay between keypresses</p><p>This may take a while, your device will be busy until the sequence has been completely transmitted!</p><p>Please \"STOP CURRENT TRANSMISSION\" before attempting to use your device or simply wait for the transmission to finish.</p><p>You can view if the brute force attempt has completed by returning to the Experimental TX page and checking the status located under \"Transmit Status\"</p></div><a href=\"/stoptx\" class=\"btn btn-danger\">STOP CURRENT TRANSMISSION</a></div></body></html>"));
        delay(50);
      }

      String bruteSTARTchar="";
      String bruteENDchar="";
      if (server.hasArg("bruteSTARTchar")&&(server.arg("bruteSTARTchar")!="")) {
        bruteSTARTchar=(server.arg("bruteSTARTchar"));
        bruteSTARTchar.replace("F1","C");
        bruteSTARTchar.replace("F2","D");
        bruteSTARTchar.replace("F3","E");
        bruteSTARTchar.replace("F4","F");
      }
      if (server.hasArg("bruteENDchar")&&(server.arg("bruteENDchar")!="")) {
        bruteENDchar=(server.arg("bruteENDchar"));
        bruteENDchar=(server.arg("bruteENDchar"));
        bruteENDchar.replace("F1","C");
        bruteENDchar.replace("F2","D");
        bruteENDchar.replace("F3","E");
        bruteENDchar.replace("F4","F");
      }

      unsigned long bruteFAILdelay=0;
      unsigned long bruteFAILS=0;
      int bruteFAILmultiplier=0;
      int bruteFAILmultiplierCURRENT=0;
      int bruteFAILmultiplierAFTER=0;
      int delayAFTERpin=0;
      int bruteFAILSmax=0;
      bruteFAILSmax=(server.arg("bruteFAILSmax")).toInt();
      delayAFTERpin=(server.arg("delayAFTERpin")).toInt();
      bruteFAILdelay=(server.arg("bruteFAILdelay")).toInt();
      bruteFAILmultiplier=(server.arg("bruteFAILmultiplier")).toInt();
      bruteFAILmultiplierAFTER=(server.arg("bruteFAILmultiplierAFTER")).toInt();

      for (int brute=bruteSTART; brute<=bruteEND; brute++) {

        if (bruteforcing==1) {
          pinHTML=String(brute);
          while (pinHTML.length()<brutePAD) {
            pinHTML="0"+pinHTML;
          }
        }

        if (bruteSTARTchar!="") {
          pinHTML=bruteSTARTchar+pinHTML;
        }

        if (bruteENDchar!="") {
          pinHTML=pinHTML+bruteENDchar;
        }
          
        for (int i=0; i<=pinHTML.length(); i++) {
          if (pinHTML.charAt(i) == '0') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"0000");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"11110000");
            }
          }
          else if (pinHTML.charAt(i) == '1') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"0001");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"11100001");
            }
          }
          else if (pinHTML.charAt(i) == '2') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"0010");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"11010010");
            }
          }
          else if (pinHTML.charAt(i) == '3') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"0011");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"11000011");
            }
          }
          else if (pinHTML.charAt(i) == '4') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"0100");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"10110100");
            }
          }
          else if (pinHTML.charAt(i) == '5') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"0101");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"10100101");
            }
          }
          else if (pinHTML.charAt(i) == '6') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"0110");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"10010110");
            }
          }
          else if (pinHTML.charAt(i) == '7') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"0111");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"10000111");
            }
          }
          else if (pinHTML.charAt(i) == '8') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"1000");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"01111000");
            }
          }
          else if (pinHTML.charAt(i) == '9') {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"1001");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"01101001");
            }
          }
          else if ((pinHTML.charAt(i) == '*')||(pinHTML.charAt(i) == 'A')) {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"1010");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"01011010");
            }
          }
          else if ((pinHTML.charAt(i) == '#')||(pinHTML.charAt(i) == 'B')) {
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"1011");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"01001011");
            }
          }
          else if (pinHTML.charAt(i) == 'C') { //F1
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"1100");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"00111100");
            }
          }
          else if (pinHTML.charAt(i) == 'D') { //F2
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"1101");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"00101101");
            }
          }
          else if (pinHTML.charAt(i) == 'E') { //F3
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"1110");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"00011110");
            }
          }
          else if (pinHTML.charAt(i) == 'F') { //F4
            if (pinBITS==4) {
              pinSEND(pinHTMLDELAY,"1111");
            }
            else if (pinBITS==8) {
              pinSEND(pinHTMLDELAY,"00001111");
            }
          }
        }

        server.handleClient();
        if (TXstatus!=1) {
          break;
        }

        bruteFAILS++;

        if (bruteFAILS>=4294967000) {
          bruteFAILS=(4294966000);
        }
        if (bruteFAILdelay>=4294967000) {
          bruteFAILdelay=(4294966000);
        }
        
        if (bruteFAILmultiplier!=0) {
          bruteFAILmultiplierCURRENT++;
          if (bruteFAILmultiplierCURRENT>=bruteFAILmultiplierAFTER) {
            bruteFAILmultiplierCURRENT=0;
            bruteFAILdelay=(bruteFAILdelay*bruteFAILmultiplier);
          }
        }
        
        if ((bruteFAILS>=bruteFAILSmax)&&(bruteFAILSmax!=0)) {
          delay(bruteFAILdelay*1000);
        }
        else {
          delay(delayAFTERpin);
        }
        
      }
      pinMode(DATA0, INPUT);
      pinMode(DATA1, INPUT);
      wg.clear();
      pinHTML="";
      pinHTMLDELAY=100;
      TXstatus=0;
      bruteforcing=0;
      brutePAD=0;
      bruteSTARTchar="";
      bruteENDchar="";
      bruteFAILdelay=0;
      bruteFAILS=0;
      bruteFAILmultiplier=0;
      bruteFAILmultiplierCURRENT=0;
      bruteFAILmultiplierAFTER=0;
      delayAFTERpin=0;
      bruteFAILSmax=0;
    }


    if (server.hasArg("binHTML")) {
      String binHTML=server.arg("binHTML");
      wg.pause();
      digitalWrite(DATA0, HIGH);
      pinMode(DATA0,OUTPUT);
      digitalWrite(DATA1, HIGH);
      pinMode(DATA1,OUTPUT);

      for (int i=0; i<=binHTML.length(); i++) {
        if (binHTML.charAt(i) == '0') {
          digitalWrite(DATA0, LOW);
          delayMicroseconds(txdelayus);
          digitalWrite(DATA0, HIGH);
        }
        else if (binHTML.charAt(i) == '1') {
          digitalWrite(DATA1, LOW);
          delayMicroseconds(txdelayus);
          digitalWrite(DATA1, HIGH);
        }
        delay(txdelayms);
      }

      pinMode(DATA0, INPUT);
      pinMode(DATA1, INPUT);
      wg.clear();

      experimentalStatus=String()+"Transmitting Binary: "+binHTML;
      binHTML="";
    }

    if (server.arg("fuzzType")=="simultaneous") {

      int fuzzTimes=0;
      dos=0;
      if ((server.arg("fuzzTimes"))=="dos") {
        dos=1;
        server.send(200, "text/html", String()+F(
        "<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:800px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.warning-section{background:#fff3cd;border-left:4px solid #ffc107;padding:20px;margin:20px 0;border-radius:4px;color:#856404}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/experimental\" class=\"btn btn-primary\">BACK TO EXPERIMENTAL TX MODE</a><div class=\"warning-section\"><p><strong>Denial of Service mode active.</strong></p><p>Transmitting D0 and D1 bits simultaneously until stopped.</p><p>This may take a while, your device will be busy until the sequence has been completely transmitted!</p><p>Please \"STOP CURRENT TRANSMISSION\" before attempting to use your device or simply wait for the transmission to finish.</p><p>You can view if the fuzzing attempt has completed by returning to the Experimental TX page and checking the status located under \"Transmit Status\"</p></div><a href=\"/stoptx\" class=\"btn btn-danger\">STOP CURRENT TRANSMISSION</a></div></body></html>"));
        delay(50);
      }
      else {
        fuzzTimes=server.arg("fuzzTimes").toInt();
        server.send(200, "text/html", String()+F(
        "<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:800px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#d1ecf1;border-left:4px solid #17a2b8;padding:20px;margin:20px 0;border-radius:4px;color:#0c5460}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/experimental\" class=\"btn btn-primary\">BACK TO EXPERIMENTAL TX MODE</a><div class=\"info-section\"><p><strong>Transmitting D0 and D1 bits simultaneously ")+fuzzTimes+F(" times.</strong></p><p>This may take a while, your device will be busy until the sequence has been completely transmitted!</p><p>Please \"STOP CURRENT TRANSMISSION\" before attempting to use your device or simply wait for the transmission to finish.</p><p>You can view if the fuzzing attempt has completed by returning to the Experimental TX page and checking the status located under \"Transmit Status\"</p></div><a href=\"/stoptx\" class=\"btn btn-danger\">STOP CURRENT TRANSMISSION</a></div></body></html>"));
        delay(50);
      }
      
      wg.pause();
      digitalWrite(DATA0, HIGH);
      pinMode(DATA0,OUTPUT);
      digitalWrite(DATA1, HIGH);
      pinMode(DATA1,OUTPUT);

      TXstatus=1;

      for (int i=0; i<=fuzzTimes || dos==1; i++) {
        digitalWrite(DATA0, LOW);
        digitalWrite(DATA1, LOW);
        delayMicroseconds(txdelayus);
        digitalWrite(DATA0, HIGH);
        digitalWrite(DATA1, HIGH);
        delay(txdelayms);
        server.handleClient();
        if (TXstatus!=1) {
          break;
        }
      }

      pinMode(DATA0, INPUT);
      pinMode(DATA1, INPUT);
      wg.clear();
      TXstatus=0;
      dos=0;

      //experimentalStatus=String()+"Transmitting D0 and D1 bits simultaneously "+fuzzTimes+" times.";
    }

    if (server.arg("fuzzType")=="alternating") {

      int fuzzTimes=0;
      dos=0;
      if ((server.arg("fuzzTimes"))=="dos") {
        dos=1;
        server.send(200, "text/html", String()+F(
        "<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:800px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.warning-section{background:#fff3cd;border-left:4px solid #ffc107;padding:20px;margin:20px 0;border-radius:4px;color:#856404}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/experimental\" class=\"btn btn-primary\">BACK TO EXPERIMENTAL TX MODE</a><div class=\"warning-section\"><p><strong>Denial of Service mode active.</strong></p><p>Transmitting bits alternating between D0 and D1 until stopped.</p><p>This may take a while, your device will be busy until the sequence has been completely transmitted!</p><p>Please \"STOP CURRENT TRANSMISSION\" before attempting to use your device or simply wait for the transmission to finish.</p><p>You can view if the fuzzing attempt has completed by returning to the Experimental TX page and checking the status located under \"Transmit Status\"</p></div><a href=\"/stoptx\" class=\"btn btn-danger\">STOP CURRENT TRANSMISSION</a></div></body></html>"));
        delay(50);
      }
      else {
        fuzzTimes=server.arg("fuzzTimes").toInt();
        server.send(200, "text/html", String()+F(
        "<html><head><meta name=\"viewport\" content=\"width=device-width,initial-scale=1\"><style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:800px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}.info-section{background:#d1ecf1;border-left:4px solid #17a2b8;padding:20px;margin:20px 0;border-radius:4px;color:#0c5460}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}</style></head><body><div class=\"container\"><a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a><br><br><a href=\"/experimental\" class=\"btn btn-primary\">BACK TO EXPERIMENTAL TX MODE</a><div class=\"info-section\"><p><strong>Transmitting ")+fuzzTimes+F(" bits alternating between D0 and D1.</strong></p><p>This may take a while, your device will be busy until the sequence has been completely transmitted!</p><p>Please \"STOP CURRENT TRANSMISSION\" before attempting to use your device or simply wait for the transmission to finish.</p><p>You can view if the fuzzing attempt has completed by returning to the Experimental TX page and checking the status located under \"Transmit Status\"</p></div><a href=\"/stoptx\" class=\"btn btn-danger\">STOP CURRENT TRANSMISSION</a></div></body></html>"));
        delay(50);
      }
      
      wg.pause();
      digitalWrite(DATA0, HIGH);
      pinMode(DATA0,OUTPUT);
      digitalWrite(DATA1, HIGH);
      pinMode(DATA1,OUTPUT);

      String binALT="";
      TXstatus=1;

      for (int i=0; i<fuzzTimes || dos==1; i++) {
        if (i%2==0) {
          digitalWrite(DATA0, LOW);
          delayMicroseconds(txdelayus);
          digitalWrite(DATA0, HIGH);
          binALT=binALT+"0";
        }
        else {
           digitalWrite(DATA1, LOW);
           delayMicroseconds(txdelayus);
           digitalWrite(DATA1, HIGH);
           binALT=binALT+"1";
        }
        delay(txdelayms);
        server.handleClient();
        if (TXstatus!=1) {
          break;
        }
      }

      pinMode(DATA0, INPUT);
      pinMode(DATA1, INPUT);
      wg.clear();
      TXstatus=0;
      dos=0;
      binALT="";
    }

    if (server.arg("pushType")=="Ground") {
      Serial.end();
      digitalWrite(3,LOW);
      pinMode(3,OUTPUT);
      delay(server.arg("pushTime").toInt());
      pinMode(3,INPUT);
      Serial.begin(9600);

      experimentalStatus=String()+"Grounding \"Push to Open\" wire for "+(server.arg("pushTime").toInt())+"ms.";
    }

    if (server.arg("pushType")=="High") {
      Serial.end();
      digitalWrite(3,HIGH);
      pinMode(3,OUTPUT);
      delay(server.arg("pushTime").toInt());
      pinMode(3,INPUT);
      Serial.begin(9600);

      experimentalStatus=String()+"Outputting 3.3V on \"Push to Open\" wire for "+(server.arg("pushTime").toInt())+"ms.";
    }

    String activeTX="";
    if (TXstatus==1) {
      
      if (pinHTML!="") {
        String currentPIN=pinHTML;
        activeTX="Brute forcing PIN: "+currentPIN+"<br><a href=\"/stoptx\" class=\"btn btn-danger\">STOP CURRENT TRANSMISSION</a>";
        currentPIN="";
      }
      else if (dos==1) {
        activeTX="Denial of Service mode active...<br><a href=\"/stoptx\" class=\"btn btn-danger\">STOP CURRENT TRANSMISSION</a>";
      }
      else {
        activeTX="Transmitting...<br><a href=\"/stoptx\" class=\"btn btn-danger\">STOP CURRENT TRANSMISSION</a>";
      }
      
    }
    else {
      activeTX="INACTIVE<br><span class=\"btn btn-secondary\" style=\"cursor:default\">NOTHING TO STOP</span>";
    }

    server.send(200, "text/html", 
      String()+
      F(
      "<!DOCTYPE HTML>"
      "<html>"
      "<head>"
      "<meta name=\"viewport\" content=\"width=device-width,initial-scale=1\">"
      "<title>Experimental TX Mode</title>"
      "<style>*{margin:0;padding:0;box-sizing:border-box}body{font-family:-apple-system,BlinkMacSystemFont,'Segoe UI',Roboto,'Helvetica Neue',Arial,sans-serif;background:#f5f5f5;color:#333;line-height:1.6;padding:20px}.container{max-width:900px;margin:0 auto;background:#fff;border-radius:8px;box-shadow:0 2px 10px rgba(0,0,0,0.1);padding:30px;margin-bottom:20px}h1{color:#2c3e50;margin-bottom:25px;font-size:28px;font-weight:600}h2{color:#34495e;margin:25px 0 15px;font-size:20px;font-weight:500;padding-bottom:10px;border-bottom:2px solid #e9ecef}.form-group{margin:20px 0}.form-group label{display:block;margin-bottom:8px;font-weight:500;color:#495057;font-size:15px}.form-group small{display:block;color:#6c757d;font-size:13px;margin-top:5px;margin-bottom:10px}input[type=\"text\"],input[type=\"password\"],input[type=\"number\"],select{width:100%;max-width:600px;padding:10px 12px;border:1px solid #ced4da;border-radius:6px;font-size:15px;font-family:inherit;transition:border-color 0.3s,box-shadow 0.3s}input[type=\"text\"]:focus,input[type=\"password\"]:focus,input[type=\"number\"]:focus,select:focus{outline:none;border-color:#007bff;box-shadow:0 0 0 3px rgba(0,123,255,0.1)}input[type=\"radio\"]{margin-right:8px;margin-left:0;width:18px;height:18px;cursor:pointer}.radio-group{margin:10px 0}.radio-group label{display:inline;font-weight:400;margin-left:5px;cursor:pointer}input[type=\"submit\"]{background:#28a745;color:#fff;padding:12px 30px;border:none;border-radius:6px;font-size:16px;font-weight:500;cursor:pointer;transition:all 0.3s;font-family:inherit;margin-top:10px}input[type=\"submit\"]:hover{background:#218838;transform:translateY(-1px);box-shadow:0 4px 8px rgba(40,167,69,0.3)}.btn{display:inline-block;padding:12px 24px;margin:8px 8px 8px 0;text-decoration:none;border-radius:6px;font-size:15px;font-weight:500;transition:all 0.3s;border:none;cursor:pointer;font-family:inherit}.btn-primary{background:#007bff;color:#fff}.btn-primary:hover{background:#0056b3;transform:translateY(-1px);box-shadow:0 4px 8px rgba(0,123,255,0.3)}.btn-danger{background:#dc3545;color:#fff}.btn-danger:hover{background:#c82333;transform:translateY(-1px);box-shadow:0 4px 8px rgba(220,53,69,0.3)}.btn-secondary{background:#6c757d;color:#fff}.btn-secondary:hover{background:#5a6268;transform:translateY(-1px);box-shadow:0 4px 8px rgba(108,117,125,0.3)}.warning-section{background:#fff3cd;border-left:4px solid #ffc107;padding:15px;margin:20px 0;border-radius:4px;color:#856404}.status-section{background:#d1ecf1;border-left:4px solid #17a2b8;padding:15px;margin:20px 0;border-radius:4px;color:#0c5460}hr{margin:30px 0;border:none;border-top:1px solid #e9ecef}</style>"
      "</head>"
      "<body>"
      "<div class=\"container\">"
      "<h1>Experimental TX Mode</h1>"
      "<a href=\"/\" class=\"btn btn-secondary\">BACK TO INDEX</a>"
      )+experimentalStatus+F("<div class=\"status-section\"><p><strong>Transmit Status:</strong></p>")+activeTX+F("</div>"
      "<div class=\"warning-section\">"
      "<p><strong>Warning:</strong> This mode is highly experimental, use at your own risk!</p>"
      "<p>Note: Timings for the Wiegand Data Pulse Width and Wiegand Data Interval may be changed on the settings page.</p>"
      "</div>"
      "<hr>"
      "<h2>Transmit Binary Data</h2>"
      "<FORM action=\"/experimental\" id=\"transmitbinary\" method=\"post\">"
      "<div class=\"form-group\">"
      "<label>Binary Data</label>"
      "<small>Typically no need to include preamble</small>"
      "<INPUT form=\"transmitbinary\" type=\"text\" name=\"binHTML\" value=\"\" pattern=\"[0-1]{1,}\" required title=\"Only 0's & 1's allowed, must not be empty\" minlength=\"1\">"
      "</div>"
      "<INPUT form=\"transmitbinary\" type=\"submit\" value=\"Transmit\">"
      "</FORM>"
      "<hr>"
      "<h2>Transmit PIN</h2>"
      "<FORM action=\"/experimental\" id=\"transmitpin\" method=\"post\">"
      "<div class=\"form-group\">"
      "<label>PIN</label>"
      "<small>Available keys 0-9, * or A, # or B, F1 or C, F2 or D, F3 or E, F4 or F</small>"
      "<INPUT form=\"transmitpin\" type=\"text\" name=\"pinHTML\" value=\"\" pattern=\"[0-9*#A-F]{1,}\" required title=\"Available keys 0-9, * or A, # or B, F1 or C, F2 or D, F3 or E, F4 or F, must not be empty\" minlength=\"1\">"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Delay between keypresses</label>"
      "<INPUT form=\"transmitpin\" type=\"number\" name=\"pinHTMLDELAY\" value=\"100\" min=\"0\" style=\"max-width:200px\"> <small>ms</small>"
      "</div>"
      "<div class=\"form-group\">"
      "<div class=\"radio-group\">"
      "<label><INPUT form=\"transmitpin\" type=\"radio\" name=\"pinBITS\" id=\"pinBITS\" value=\"4\" checked required> 4bit Wiegand PIN Format</label><br>"
      "<label><INPUT form=\"transmitpin\" type=\"radio\" name=\"pinBITS\" id=\"pinBITS\" value=\"8\" required> 8bit Wiegand PIN Format</label>"
      "</div></div>"
      "<INPUT form=\"transmitpin\" type=\"submit\" value=\"Transmit\">"
      "</FORM>"
      "<hr>"
      "<h2>Bruteforce PIN</h2>"
      "<FORM action=\"/experimental\" id=\"brutepin\" method=\"post\">"
      "<div class=\"form-group\">"
      "<label>Delay between keypresses</label>"
      "<INPUT form=\"brutepin\" type=\"number\" name=\"pinHTMLDELAY\" value=\"3\" min=\"0\" style=\"max-width:200px\"> <small>ms</small>"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Delay between entering complete PINs</label>"
      "<INPUT form=\"brutepin\" type=\"number\" name=\"delayAFTERpin\" value=\"0\" min=\"0\" style=\"max-width:200px\"> <small>ms</small>"
      "</div>"
      "<div class=\"form-group\">"
      "<label>PIN begins with character(s)</label>"
      "<INPUT form=\"brutepin\" type=\"text\" name=\"bruteSTARTchar\" value=\"\" pattern=\"[0-9*#A-F]{0,}\" title=\"Available keys 0-9, * or A, # or B, F1 or C, F2 or D, F3 or E, F4 or F\" style=\"max-width:200px\">"
      "</div>"
      "<div class=\"form-group\">"
      "<label>PIN start position</label>"
      "<INPUT form=\"brutepin\" type=\"number\" name=\"bruteSTART\" value=\"0000\" min=\"0\" style=\"max-width:200px\">"
      "</div>"
      "<div class=\"form-group\">"
      "<label>PIN end position</label>"
      "<INPUT form=\"brutepin\" type=\"number\" name=\"bruteEND\" value=\"9999\" min=\"0\" style=\"max-width:200px\">"
      "</div>"
      "<div class=\"form-group\">"
      "<label>PIN ends with character(s)</label>"
      "<INPUT form=\"brutepin\" type=\"text\" name=\"bruteENDchar\" value=\"#\" pattern=\"[0-9*#A-F]{0,}\" title=\"Available keys 0-9, * or A, # or B, F1 or C, F2 or D, F3 or E, F4 or F\" style=\"max-width:200px\">"
      "</div>"
      "<div class=\"form-group\">"
      "<small>NOTE: The advanced timing settings listed below override the \"Delay between entering complete PINs\" setting (listed above) when the conditions listed below are met.</small>"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Number of failed PIN attempts (X) before a delay</label>"
      "<INPUT form=\"brutepin\" type=\"number\" name=\"bruteFAILSmax\" value=\"0\" min=\"0\" style=\"max-width:200px\">"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Delay in seconds (Y) after [X] failed PINs</label>"
      "<INPUT form=\"brutepin\" type=\"number\" name=\"bruteFAILdelay\" value=\"0\" min=\"0\" style=\"max-width:200px\"> <small>s</small>"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Advanced Timing Multiplier</label>"
      "<small>Multiply delay [Y] by <INPUT form=\"brutepin\" type=\"number\" name=\"bruteFAILmultiplier\" value=\"0\" min=\"0\" style=\"max-width:100px\"> after every <INPUT form=\"brutepin\" type=\"number\" name=\"bruteFAILmultiplierAFTER\" value=\"0\" min=\"0\" style=\"max-width:100px\"> failed pin attempts</small>"
      "</div>"
      "<div class=\"form-group\">"
      "<div class=\"radio-group\">"
      "<label><INPUT form=\"brutepin\" type=\"radio\" name=\"pinBITS\" id=\"pinBITS\" value=\"4\" checked required> 4bit Wiegand PIN Format</label><br>"
      "<label><INPUT form=\"brutepin\" type=\"radio\" name=\"pinBITS\" id=\"pinBITS\" value=\"8\" required> 8bit Wiegand PIN Format</label>"
      "</div></div>"
      "<INPUT form=\"brutepin\" type=\"submit\" value=\"Transmit\">"
      "</FORM>"
      "<hr>"
      "<h2>Fuzzing</h2>"
      "<FORM action=\"/experimental\" id=\"fuzz\" method=\"post\">"
      "<div class=\"form-group\">"
      "<label>Number of bits</label>"
      "<INPUT form=\"fuzz\" type=\"number\" name=\"fuzzTimes\" value=\"100\" min=\"1\" max=\"2147483647\">"
      "</div>"
      "<div class=\"form-group\">"
      "<div class=\"radio-group\">"
      "<label><INPUT form=\"fuzz\" type=\"radio\" name=\"fuzzType\" id=\"simultaneous\" value=\"simultaneous\" required> Transmit a bit simultaneously on D0 and D1 (X bits per each line)</label><br>"
      "<label><INPUT form=\"fuzz\" type=\"radio\" name=\"fuzzType\" id=\"alternating\" value=\"alternating\"> Transmit X bits alternating between D0 and D1 each bit (01010101, etc)</label>"
      "</div></div>"
      "<INPUT form=\"fuzz\" type=\"submit\" value=\"Fuzz\">"
      "</FORM>"
      "<hr>"
      "<h2>Denial Of Service Mode</h2>"
      "<FORM action=\"/experimental\" id=\"dos\" method=\"post\">"
      "<INPUT hidden=\"1\" form=\"dos\" type=\"text\" name=\"fuzzTimes\" value=\"dos\">"
      "<div class=\"form-group\">"
      "<label>Type of Attack</label>"
      "<div class=\"radio-group\">"
      "<label><INPUT form=\"dos\" type=\"radio\" name=\"fuzzType\" id=\"simultaneous\" value=\"simultaneous\" required> Transmit a bit simultaneously on D0 and D1 until stopped</label><br>"
      "<label><INPUT form=\"dos\" type=\"radio\" name=\"fuzzType\" id=\"alternating\" value=\"alternating\"> Transmit bits alternating between D0 and D1 each bit (01010101, etc) until stopped</label>"
      "</div></div>"
      "<INPUT form=\"dos\" type=\"submit\" value=\"Start DoS\">"
      "</FORM>"
      "<hr>"
      "<h2>Push Button for Door Open</h2>"
      "<div class=\"warning-section\">"
      "<p>Connect \"Push to Open\" wire from the reader to the RX pin (GPIO3) on the programming header on ESP-RFID-Tool.</p>"
      "<p><strong>Warning!</strong> Selecting the wrong trigger signal type may cause damage to the connected hardware.</p>"
      "</div>"
      "<FORM action=\"/experimental\" id=\"push\" method=\"post\">"
      "<div class=\"form-group\">"
      "<label>Time in ms to push the door open button</label>"
      "<INPUT form=\"push\" type=\"text\" name=\"pushTime\" value=\"50\" pattern=\"^[1-9]+[0-9]*$\" required title=\"Must be a number > 0, must not be empty\" minlength=\"1\" style=\"max-width:200px\">"
      "</div>"
      "<div class=\"form-group\">"
      "<label>Does the wire expect a High or Low signal to open the door</label>"
      "<div class=\"radio-group\">"
      "<label><INPUT form=\"push\" type=\"radio\" name=\"pushType\" id=\"Ground\" value=\"Ground\" checked required> Low Signal [Ground]</label><br>"
      "<label><INPUT form=\"push\" type=\"radio\" name=\"pushType\" id=\"Ground\" value=\"High\" required> High Signal [3.3V]</label>"
      "</div></div>"
      "<INPUT form=\"push\" type=\"submit\" value=\"Push\">"
      "</FORM>"
      "</div>"
      "</body>"
      "</html>"
      )
    );

    if (server.args()>=1) {
      if (safemode==1) {
        delay(50);
        ESP.restart();
      }
    }

  });

  server.begin();
  WiFiClient client;
  client.setNoDelay(1);

  MDNS.begin("ESP");

  httpUpdater.setup(&httpServer, update_path, update_username, update_password);
  httpServer.begin();

  MDNS.addService("http", "tcp", 1337);
  
  if (ftpenabled==1){
    ftpSrv.begin(String(ftp_username),String(ftp_password));
  }

  pinMode(LED_BUILTIN, OUTPUT);  // LED
  if (ledenabled==1){
    digitalWrite(LED_BUILTIN, LOW);
  }
  else{
    digitalWrite(LED_BUILTIN, HIGH);
  }

}

///////////////////////////////////////////////////////
// LOOP function
void loop()
{
  if (ftpenabled==1){
    ftpSrv.handleFTP();
  }
  server.handleClient();
  httpServer.handleClient();
  while (Serial.available()) {
    String cmd = Serial.readStringUntil(':');
    if(cmd == "ResetDefaultConfig"){
      loadDefaults();
      ESP.restart();
    }
  }

  if(wg.available()) {
    wg.pause();             // pause Wiegand pin interrupts
    LogWiegand(wg);
    wg.clear();             // compulsory to call clear() to enable interrupts for subsequent data
    if (safemode==1) {
      ESP.restart();
    }
  }

}
