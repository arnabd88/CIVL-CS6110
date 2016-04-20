GMC: Generic Model Checker

Provides general utilities for building model checkers, such
as a generic depth-first search algorithm.

======================= Installation from source =======================

1. Install a Java 7 SDK if you have not already.  Go to
http://www.oracle.com/technetwork/java/javase/downloads/ for the
latest from Oracle.  On linux, you can optionally sudo apt-get install
openjdk-7-jdk. 

2. Install Apache ant, if you don't already have it
(http://ant.apache.org).

3. Download the tgz archive of VSL dependencies from 
   http://vsl.cis.udel.edu/tools/vsl_depend,
   choosing the right .tgz according to your platform:
	
	vsl_linux32-1.0.tgz	- 32-bit linux
	vsl_linux64-1.0.tgz	- 64-bit linux
	vsl_osx64-1.0.tgz	- 64-bit osx
	
   Unzip the .tgz file and you will have the folder vsl.
   Move vsl to /opt (you might need to use “sudo” for this.
   Also, if you don't already have a directory called /opt, 
   you will have to create it with mkdir /opt).

   Suppose that you put the .tgz file (or .tar file if your browser
   unzipped it automatically to a .tar file) in the directory $Download.
   You can use the following commands:

   		$ cd $Download
   		$ tar xzf YourTgzOrTarFile vsl
   		$ sudo mv vsl /opt

   Now you can type "ls /opt/vsl", and the output should be

   		README.txt    lib        licenses    src
   		
4. svn checkout svn://vsl.cis.udel.edu/gmc/trunk gmc

5. cd gmc

6. If your VSL dependencies path is not in /opt/vsl, then you need
to create a build.properties file by copying the content from
build_default.properties and modifying the value of entry "root"
to be the path to your VSL dependencies folder. The newly created file
build.properties will automatically be used by ant to to build the .jar file.

7. Type "ant" and everything should build without warnings or errors
and produce gmc.jar.  Type "ant test" to run a JUnit test suite.  All
tests should pass.

If there are any problems, email siegel at udel dot edu.

============== Installation from source using Eclipse ==================

1. Start with Eclipse IDE for Java/EE developers, available at
http://www.eclipse.org/downloads/
You need at least version Kepler (which comes with JUnit 4.11)

2. Do steps 1-3 from above if you have not already.

3. Install an SVN plugin in Eclipse (such as Subversive) if you have
not already.

4. From within Eclipse, select New Project...from SVN.  The archive is
svn://vsl.cis.udel.edu/gmc.  After entering that, open it up
(i.e., "Browse" the repository) and select the "trunk".
You want to check out the trunk only---not the entire repository.

5. Check out the trunk, and create the project using the New Java
Project Wizard as usual, naming it "GMC". The .project, .classpath,
and other Eclipse meta-data are already in the SVN archive, saving you
a bunch of work.

6. If your VSL dependencies path is not in /opt/vsl, then you need
to create a build.properties file by copying the content from
build_default.properties and modifying the value of entry "root"
to be the path to your VSL dependencies folder. The newly created file
build.properties will automatically be used by ant to to build the .jar file.

7. Do a clean build.  Everything should compile.  Generate the gmc.jar
by right-clicking (or ctrl-click on OS X) the build.xml file and
Run As->Ant Build.  

8. Go to Run->Run Configurations.... Create a new JUnit configuration.
Name it GMC Tests. Select "Run all tests in the selected project..."
and navigate to the folder "test" in the SARL project.
The Test runner should be JUnit 4. Under the Arguments tab, type
"-ea" (without the quotes) in the VM arguments area (to enable assertion
checking).
