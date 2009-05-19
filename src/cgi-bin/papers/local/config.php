<?php if (!defined('PmWiki')) exit();
$WikiTitle = "PLClub Wiki";
$PageLogoUrl = "http://www.cis.upenn.edu/~plclub/images/plclub-logo_small.png";

$DefaultPasswords['admin'] = crypt('9x1h3__g');

$OpenPassword = crypt('lambda');
$DefaultPasswords['read'] = $OpenPassword;
$DefaultPasswords['edit'] = $OpenPassword;

$EnableUpload = 0;

putenv("TZ=EST5EDT");
//$TimeFmt = '%B %d, %Y, at %I:%M %p EST';

?>