General instructions on usage.

- To rebuild the website run

% make all

  this will create a copy of publishable version of the website in "dest".

- To publish the website run

% make USER=<username> live

  This will first commit your working copy, so as to help avoid races on
  the actual website.  It will then transfer the contents of the "dest"
  directory via rsync over ssh.  The variable <username> should be your
  SEAS username and rsync will ask you for your SEAS password.

- To update your local copy you can just run

% make update

- To commit your local copy you can just run

% make commit
