<?xml version="1.0" encoding="UTF-8"?>
<!DOCTYPE stylesheet SYSTEM "submissions.dtd">
<xsl:stylesheet xmlns:xsl="http://www.w3.org/1999/XSL/Transform"
 xmlns="http://www.w3.org/1999/xhtml" version="1.0">

<xsl:preserve-space elements="*"/>

<xsl:output method="html"
doctype-public="-//W3C//DTD XHTML 1.0 Strict//EN"
doctype-system="DTD/xhtml1-strict.dtd" />

<xsl:template match="/">
  <html xmlns="http://www.w3.org/1999/xhtml">
  <head>
    <title>POPLmark: Submissions</title>
    <meta http-equiv="Content-Type" content="text/html; charset=UTF-8" />
    <link rel="stylesheet" href="style.css" type="text/css" />
  </head>
  <body>

  <div class="content">

    <h1><img style="float: left; border: solid 1px black; margin-right: 10px"
             src="./POPLmark-logo-64.png" alt="POPLmark" />
       Submissions 
    </h1>

    <div style="clear: both; height: 0.1em"></div>

    <h2>Current submissions</h2>

    <p>Submissions should be sent to the <a href="http://lists.seas.upenn.edu/mailman/listinfo/poplmark">mailing list</a>.</p>
  
    <xsl:call-template name="entries" />

    <h2>Evaluation</h2>

    <p><em><b>Important:</b> The scores and evaluations here are provisional and
    subject to revision on the basis of further discussion.</em></p>

    <p>The scores in the following table attempt to summarize our impressions of
    each submission according to the criteria listed; by no means do they
    constitute a definitive evaluation.  The criteria here are an elaboration of
    the ones listed in Section 2.3 of the challenge, and descriptions can be
    found below the table.  While the meaning of the scores depends on the
    particular criteria in question, we generally intend them to convey the
    following:</p>

    <ul>

      <li><b>A</b>: exactly the sort of thing we're looking for</li>

      <li><b>B</b>: useable but a lot of trouble</li>

      <li><b>C</b>: useable only with heroic effort (we will prefer to stick
      with paper-and-pencil until the situation improves)</li>

      <li><b>Yes</b>: challenge completed</li>

      <li><b>Close</b>: challenge essentially completed, but we have some
      reservations</li>

      <li><b>-</b>: unable to evaluate or not completed</li>

      <li><b>?</b>: not evaluated yet</li>
    </ul>

    <xsl:call-template name="gradetable" />

<!--
    <h2>Lines of Code </h2>

    <p>As a rough measure of the work involved in developing each solution, we
    include the number of lines of code needed for each challenge problem.  The
    values are intended to be <em>totals</em>; for example, the lines of code
    counted for the definitions of Challenge 2b includes the code needed to
    define (in their entirety) the subtyping, typing, and evaluation
    relations.</p>

    <xsl:call-template name="codetable" />
-->

    <h2>Descriptions of the Evaluation Criteria</h2>

    <dl>
      <dt><a id="desc-drag"></a>Drag</dt>
      <dd>The degree to which proofs (and to a lesser extent, definitions) are
      cluttered with elements specific to the term representation technique.
      These elements tend to obscure the main argument of proofs.  Less clutter
      is preferred.</dd>

      <dt><a id="desc-accessibility"></a>Accessibility</dt>
      <dd>The ease with which users with little or no experience with
      the technology in question (system and representation technique) can
      convince themselves that the formal presentation corresponds with the
      intended meaning of the paper presentation.  More ease is better.   
      </dd>

      <dt><a id="desc-transparency"></a>Transparency</dt>
      <dd>The degree to which it is clear that the statements of definitions,
      lemmas, and theorems correspond to ones on paper.  It should be obvious
      that the statements capture exactly the meaning intended on paper.</dd>
      
      <dt><a id="desc-challenge1a"></a>Challenge 1a</dt>
      <dd>The proof of transitivity of the algorithmic subtyping relation for
      pure F<sub>&lt;:</sub>.</dd>

      <dt><a id="desc-challenge1b"></a>Challenge 1b</dt>
      <dd>The proof of transitivity of the algorithmic subtyping relation for
      pure F<sub>&lt;:</sub> extended with records.</dd>

      <dt><a id="desc-challenge2a"></a>Challenge 2a</dt>
      <dd>Type soundness for pure F<sub>&lt;:</sub>.</dd>

      <dt><a id="desc-challenge2b"></a>Challenge 2b</dt>
      <dd>Type soundness for pure F<sub>&lt;:</sub> extended with records and
      record patterns.</dd>

      <dt><a id="desc-challenge3"></a>Challenge 3</dt>
      <dd>Testing and animation with respect to the operational semantics of
      F<sub>&lt;:</sub> (including records).</dd>
   </dl>

   <div class="footer">
     Last updated: <xsl:comment>#flastmod virtual="submissions.shtml"</xsl:comment><br />
     <a href="http://validator.w3.org/check?uri=referer">Valid XHTML</a>
     and <a href="http://jigsaw.w3.org/css-validator/check/referer">Valid CSS</a>
   </div>
  </div> 
  </body>
  </html>

</xsl:template>
    
<xsl:template name="entries">
  <ul>
  <xsl:for-each select="submissions/submission">
    <li>
      <a href="{file/node()}">Submission</a> by 
      <xsl:copy-of select="authors/node()|author/node()" />
      <xsl:if test="subfiles">
        (also available as individual files:
        <xsl:for-each select="subfiles/subfile">
          <a href="{file/node()}"><xsl:copy-of select="name/node()" /></a>
        <xsl:if test="position()!=last()">
          <xsl:text>, </xsl:text>
        </xsl:if>
        </xsl:for-each>)
      </xsl:if>    
      </li>
  </xsl:for-each>
  </ul>
</xsl:template>

<xsl:template name="gradetable">
 <table class="gd" style="margin:0 auto;">
  
  <tr><td></td>
  <xsl:for-each select="submissions/submission">
  <th style="text-align:center;">Solution <xsl:value-of select="position()" /><br />
    <a href="{file/node()}"><xsl:copy-of select="name/node()" /></a>
  </th>
  </xsl:for-each>
  </tr>
  
  <tr>
  <th>System/Logic</th> 
  <xsl:for-each select="submissions/submission">
    <td class="gd"><xsl:copy-of select="system/node()" /></td>
  </xsl:for-each>
  </tr>
  
  <tr>
  <th>Term representation</th> 
  <xsl:for-each select="submissions/submission">
    <td class="gd"><xsl:copy-of select="representation/node()" /></td>
  </xsl:for-each>
  </tr>
  
  <tr> 
  <th><a href="#desc-drag">Drag</a></th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#drag"><xsl:copy-of select="drag/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>
  
  <tr> 
  <th><a href="#desc-Accessibility">Accessibility</a></th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#acess"><xsl:copy-of select="accessibility/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>
  
  <tr> 
  <th><a href="#desc-transparency">Transparency</a></th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#transparency"><xsl:copy-of select="transparency/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>
  
  <tr> 
  <th><a href="#desc-challenge1a">Challenge 1a</a></th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#challenge1a"><xsl:copy-of select="challenge1a/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>
  
  <tr> 
  <th><a href="#desc-challenge1b">Challenge 1b</a></th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#challenge1b"><xsl:copy-of select="challenge1b/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>
  
  <tr> 
  <th><a href="#desc-challenge2a">Challenge 2a</a></th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#challenge2a"><xsl:copy-of select="challenge2a/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>

  <tr> 
  <th><a href="#desc-challenge2b">Challenge 2b</a></th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#challenge2b"><xsl:copy-of select="challenge2b/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>

  <tr> 
  <th><a href="#desc-challenge3">Challenge 3</a></th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#challenge3"><xsl:copy-of select="challenge3/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>
  
  <tr> 
  <th>Overall</th>
  <xsl:for-each select="submissions/submission">
    <td class="gd">
      <a href="{gradefile/node()}#overall"><xsl:copy-of select="overall/node()" /></a>
    </td>
  </xsl:for-each>
  </tr>  
 </table>    
</xsl:template>

<xsl:template name="codetable">
 <table class="gd" style="margin:0 auto;">
 </table>    
</xsl:template>


</xsl:stylesheet>

<!--


<tr><th colspan="2"><a href="#desc-transparency">Transparency</a></th> <td
class="gd"><a href="./poplmark/vouillon-coq.shtml#transparency">B+</a></td> 
<td class="gd"><a href="./poplmark/cmu-twelf.shtml#transparency">-</a></td>
<td class="gd">?</td>
</tr>

<tr>
<th colspan="2"><a href="#desc-challenge1a">Challenge 1a</a></th>   <td
class="gd"><a href="./poplmark/vouillon-coq.shtml#challenges">Close</a></td> 
<td class="gd"><a href="./poplmark/cmu-twelf.shtml#challenges1a">Yes</a></td>
<td class="gd">-</td>
</tr>

<tr>
<th colspan="2"><a href="#desc-challenge1b">Challenge 1b</a></th>   <td class="gd">?</td> <td 
class="gd"><a href="./poplmark/cmu-twelf.shtml#challenges1b">Yes</a></td>
<td class="gd">-</td>
</tr>

<tr>
<th colspan="2"><a href="#desc-challenge2a">Challenge 2a</a></th> <td
class="gd"><a href="./poplmark/vouillon-coq.shtml#challenges">Close</a></td> 
<td class="gd"><a href="./poplmark/cmu-twelf.shtml#challenges2a">Yes</a></td>
<td class="gd">-</td>
</tr>

<tr>
<th colspan="2"><a href="#desc-challenge2b">Challenge 2b</a></th>               <td class="gd">?</td> 
<td class="gd"><a 
href="./poplmark/cmu-twelf.shtml#challenges2b">Yes</a></td>
<td class="gd">-</td>
</tr>

<tr>
<th colspan="2"><a href="#desc-challenge3">Challenge 3</a></th>              <td class="gd">-</td> <td 
class="gd"><a href="./poplmark/cmu-twelf.shtml#challenges3">-</a></td>
<td class="gd">?</td>
</tr>

<tr>
<th colspan="2">Overall</th>   <td class="gd">-</td>  <td class="gd"><a 
href="./poplmark/cmu-twelf.shtml#overall">-</a></td>
<td class="gd">-</td>
</tr>

<tr><th colspan="2">Additional comments available?</th> <td class="gd"><a
href="./poplmark/vouillon-coq.shtml">Yes</a></td>
<td class="gd"><a href="./poplmark/cmu-twelf.shtml">Yes</a></td>
<td class="gd">No</td>
</tr>

</table>


<table class="gd" style="margin:0 auto;">
<tr><td></td><td></td><th style="text-align:center;">Solution 1<br /><a href="./poplmark/vouillon-coq.v">Vouillon</a></th><th 
style="text-align: center;">Solution 2<br /><a href="./poplmark/cmu-twelf.tar.gz">Carnegie 
Mellon</a></th>
<th style="text-align: center;">Solution 3<br /><a
href="./poplmark/mf266-alpha-prolog.tar.gz">Fairbairn</a></th></tr>

<tr>
<th rowspan="2">Challenge 1a</th>  <th class="sub">Definitions</th> <td
class="gd">?</td> <td class="gd">?</td><td class="gd">-</td>
</tr>
<tr>
<th class="sub">Proofs</th>                       <td class="gd">?</td> <td
class="gd">?</td><td class="gd">-</td>
</tr>

<tr>
<th rowspan="2">Challenge 1b</th>   <th class="sub">Definitions</th><td
class="gd">-</td> <td class="gd">?</td><td class="gd">-</td>
</tr>
<tr>
<th class="sub">Proofs</th>                       <td class="gd">-</td> <td
class="gd">?</td><td class="gd">-</td>
</tr>

<tr>
<th rowspan="2">Challenge 2a</th><th class="sub">Definitions</th>
<td class="gd">?</td> <td class="gd">?</td><td class="gd">-</td>
</tr>
<tr>
<th class="sub">Proofs</th>                       <td class="gd">?</td> <td
class="gd">?</td><td class="gd">-</td>
</tr>

<tr>
<th rowspan="2">Challenge 2b</th><th class="sub">Definitions</th>
<td class="gd">-</td> <td class="gd">?</td><td class="gd">-</td>
</tr>
<tr>
<th class="sub">Proofs</th>                       <td class="gd">-</td> <td
class="gd">?</td><td class="gd">-</td>
</tr>

<tr>
<th colspan="2">Challenge 3</th>              <td class="gd">-</td> <td
class="gd">?</td><td class="gd">?</td>
</tr>

</table>




-->
