<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE stylesheet SYSTEM "schedule.dtd">
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform" 
                xmlns="http://www.w3.org/1999/xhtml" 
                version="1.1">

<xsl:preserve-space elements="*"/>

<xsl:param name="semester"></xsl:param>
<xsl:param name="file"></xsl:param>

<xsl:variable name="months">
<months>
<month num="01" name="January" abbrev="Jan" days="31" />
<!-- FIX - Doesn't correctly handle leap years yet -->
<month num="02" name="February" abbrev="Feb" days="29" />
<month num="03" name="March" abbrev="Mar" days="31" />
<month num="04" name="April" abbrev="Apr" days="30" />
<month num="05" name="May" abbrev="May" days="31" />
<month num="06" name="June" abbrev="Jun" days="30" />
<month num="07" name="July" abbrev="Jul" days="31" />
<month num="08" name="August" abbrev="Aug" days="31" />
<month num="09" name="September" abbrev="Sep" days="30" />
<month num="10" name="October" abbrev="Oct" days="31" />
<month num="11" name="November" abbrev="Nov" days="30" />
<month num="12" name="December" abbrev="Dec" days="31" />
</months>
</xsl:variable>

<xsl:template name="formatdaymonth">
  <xsl:param name="num" /> 
  <xsl:choose>
    <xsl:when test="string-length($num)=1">0<xsl:value-of select="$num" /></xsl:when>
    <xsl:otherwise><xsl:value-of select="$num" /></xsl:otherwise>
  </xsl:choose>
</xsl:template>

<xsl:template name="htmldate">
  <xsl:param name="date" />
  
  <xsl:variable name="year" select="substring($date,1,4)" />
  <xsl:variable name="month" select="substring($date,5,2)" />
  <xsl:variable name="day" select="substring($date,7,2)" />

  
  <xsl:value-of select="$months/node()/*[@num=$month]/@abbrev" /><xsl:text>&nbsp;</xsl:text><xsl:value-of select="$day" />

</xsl:template>

<xsl:template name="incdate">
  <xsl:param name="date" />
  
  <xsl:variable name="year" select="substring($date,1,4)" />
  <xsl:variable name="month" select="substring($date,5,2)" />
  <xsl:variable name="day" select="substring($date,7,2) + 7" />

  <xsl:variable name="mdays" select="$months/node()/*[@num=$month]/@days" />
 
  <xsl:choose>
  <!--
    <xsl:when test="$month='02'">
      <xsl:choose>
        <xsl:when test="($year mod 4)=0">
          
        </xsl:when>
        <xsl:otherwise>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:when>
    -->
    <xsl:when test="$month='12'">
      <xsl:choose>
        <xsl:when test="$day > 31">
          <xsl:value-of select="$year + 1" />01<xsl:call-template name="formatdaymonth"><xsl:with-param name="num" select="$day - 31" /></xsl:call-template>
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$year" /><xsl:call-template name="formatdaymonth"><xsl:with-param name="num" select="$month" /></xsl:call-template><xsl:call-template name="formatdaymonth"><xsl:with-param name="num" select="$day" /></xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:when>
    
    <xsl:otherwise>
      <xsl:choose>
        <xsl:when test="$mdays &lt; $day">
          <xsl:value-of select="$year" /><xsl:call-template name="formatdaymonth"><xsl:with-param name="num" select="$month + 1" /></xsl:call-template><xsl:call-template name="formatdaymonth"><xsl:with-param name="num" select="$day - $mdays" /></xsl:call-template>
          
        </xsl:when>
        <xsl:otherwise>
          <xsl:value-of select="$year" /><xsl:call-template name="formatdaymonth"><xsl:with-param name="num" select="$month" /></xsl:call-template><xsl:call-template name="formatdaymonth"><xsl:with-param name="num" select="$day" /></xsl:call-template>
        </xsl:otherwise>
      </xsl:choose>
    </xsl:otherwise>
  </xsl:choose>
</xsl:template> 

<xsl:output method="html"
doctype-public="-//W3C//DTD XHTML 1.0 Strict//EN"
doctype-system="DTD/xhtml1-strict.dtd" />

<xsl:template match="/">
  <html xmlns="http://www.w3.org/1999/xhtml">
<head>
  <title>PLClub <xsl:value-of select="$semester" /> Lunch Schedule</title>
  <meta http-equiv="Content-Type" content="text/html; charset=utf-8" />
  <link href="http://www.cis.upenn.edu/proj/plclub/style.css" rel="stylesheet" type="text/css" />
</head>
<body>

<table cellpadding="10" cellspacing="4" style="border:0; width: 100%">
  <tr style="vertical-align: bottom;">
    <td colspan="2" style="background: #CFED74; width: 100%;">
        <h1 style="vertical-align: bottom;">PLClub <xsl:value-of select="$semester" /> Lunch Schedule</h1>
    </td>
  </tr>
  <tr>
    <td colspan="2" id="content">
      <table border="0" style="margin-left: auto; margin-right:auto;" cellpadding="5" cellspacing="5">
  
  <tr style="background: #FFFF99;">
    <td width="78" align="right"><div align="left">Date</div></td>
    <td width="220">Speaker</td>
    <td width="320">Topic</td>
    <td width="320">Other</td>
  </tr>
    
      <xsl:call-template name="talks">
        <xsl:with-param name="start" select="schedule/start-date/node()" />
        <xsl:with-param name="end" select="schedule/end-date/node()" />
      </xsl:call-template>
      
      
      </table>
    </td>
  </tr>

  <tr style="height: 3em; vertical-align:bottom;" >
    <td style="background: #B4D7E9; width: 20%">
        <small>Last modified: <xsl:comment><xsl:text>#flastmod virtual="</xsl:text><xsl:value-of select="$file" /><xsl:text>"</xsl:text></xsl:comment></small>
    </td>
    <td style="background: #CFED74; width: 80%;">
        <table width="100%"><tr>
        <td style="vertical-align: bottom;">
        <a href="http://www.cis.upenn.edu">Computer &amp; Information Science</a><br />
        <a href="http://www.seas.upenn.edu">School of Engineering and Science</a><br />
        <a href="http://www.upenn.edu">University of Pennsylvania</a>
        </td>
        <td style="text-align: right; vertical-align: bottom; width:180px;">
      <a href="http://validator.w3.org/check?uri=referer">
         <img style="border:0;width:88px;height:31px"
          src="http://www.w3.org/Icons/valid-xhtml11"
          alt="Valid XHTML 1.1!" /></a>
      <a href="http://jigsaw.w3.org/css-validator/">
         <img style="border:0;width:88px;height:31px"
          src="http://jigsaw.w3.org/css-validator/images/vcss"
          alt="Valid CSS!" />
      </a>

        </td>
        </tr></table>
    </td>
  </tr>
</table>
</body>
</html>
</xsl:template>
    
<xsl:template name="talks">
  <xsl:param name="start" />       
  <xsl:param name="current" select="$start" />       
  <xsl:param name="parity" select="'even'" />       
  <xsl:param name="end" />
 
  <xsl:element name="tr">
    <xsl:choose>
      <xsl:when test="schedule/cancel[date=$current]">
       <xsl:attribute name="style"><xsl:text>background: #AAAAAA;</xsl:text></xsl:attribute>
      </xsl:when>
      <xsl:when test="$parity='even'">
       <xsl:attribute name="style"><xsl:text>background: #CCFFFF;</xsl:text></xsl:attribute>
      </xsl:when> 
      <xsl:when test="$parity='odd'">
       <xsl:attribute name="style"><xsl:text>background: #BBEEEE;</xsl:text></xsl:attribute>
      </xsl:when> 
    </xsl:choose>
    
    <td align="right">
      <xsl:call-template name="htmldate">
        <xsl:with-param name="date"><xsl:value-of select="$current " /></xsl:with-param>
      </xsl:call-template>
      </td>

    <xsl:choose>
      <xsl:when test="schedule/cancel[date=$current]">
            <td colspan="3">
             <xsl:copy-of select="schedule/cancel[date=$current]/reason/node()" />
           </td>
      </xsl:when>
      <xsl:when test="schedule/talk[date=$current]">
        <td><xsl:copy-of select="schedule/talk[date=$current]/speaker/node()" /></td>
        <xsl:choose>
          <xsl:when test="schedule/talk[date=$current]/link">
            <td>
            <a><xsl:attribute name="href"><xsl:value-of select="schedule/talk[date=$current]/link/node()" /></xsl:attribute>
             <xsl:copy-of select="schedule/talk[date=$current]/topic/node()" />
             </a>
             </td>
          </xsl:when>
          <xsl:otherwise>
            <td><xsl:copy-of select="schedule/talk[date=$current]/topic/node()" /></td>
          </xsl:otherwise>  
        </xsl:choose>  
        <xsl:choose>
          <xsl:when test="schedule/talk[date=$current]/other">
            <td><xsl:copy-of select="schedule/talk[date=$current]/other/node()" /></td>
          </xsl:when>
          <xsl:otherwise>
            <td>&nbsp;</td>
          </xsl:otherwise>
        </xsl:choose>  
      
      </xsl:when>
      <xsl:otherwise>
        <td>&nbsp;</td>
        <td>&nbsp;</td>
        <td>&nbsp;</td>
      </xsl:otherwise>
    </xsl:choose>
      
  </xsl:element>

  <xsl:variable name="newdate">
    <xsl:call-template name="incdate">
    <xsl:with-param name="date" select="$current" />
    </xsl:call-template>
  </xsl:variable>
  
  <xsl:variable name="newparity">
    <xsl:choose>
      <xsl:when test="$parity='even'">odd</xsl:when>
      <xsl:when test="$parity='odd'">even</xsl:when>
    </xsl:choose>
  </xsl:variable>

  
  <xsl:if test="$newdate &lt;= $end">
  <xsl:text>
  </xsl:text>
    <xsl:call-template name="talks">
      <xsl:with-param name="start" select="$start" />
      <xsl:with-param name="current" select="$newdate" />
      <xsl:with-param name="parity" select="$newparity" />
      <xsl:with-param name="end" select="$end" />
    </xsl:call-template>
  </xsl:if>  
</xsl:template>


</xsl:stylesheet>

