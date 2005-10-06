Requirements
------------

To "rebuild" the web page you must have the following software installed

  - omake (...)
  - j2sdk 1.4 or above (...)
  - bibtex2html (...)
  - bib2bib (...)
  - wget (...)
  - rsync (...)
  - ssh (...)

Additionally, you will need the ability to log in as the SEAS user
"plclub".  This can be done by either having the password, or by having
a ssh key added to plclub's .ssh/authorized_keys or .ssh/authorized_keys2
file.


General instructions on usage
-----------------------------

- To rebuild the website run

% omake make build

  this will create a copy of publishable version of the website in "dest".

- To publish the website run

% omake live

  This will transfer the contents of the "dest" directory via rsync
  over ssh.  At this point ssh may ask you for the plclub user's password
  or your ssh key's password.

- To update your local copy you can just run

% omake update

- To commit your local copy you can just run

% omake commit
