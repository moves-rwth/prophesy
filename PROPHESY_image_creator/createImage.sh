#!/bin/bash

# Create image script
# Originally from HASDEL (http://moves.rwth-aachen.de/research/projects/hasdel/)

# This image file one needs to be in the same directory as this file
PRESEED=$1
FINISHER=$2
DEBCONFIGFILE=$3
DEBIAN_ISO=$"debian-7.8.0-amd64-netinst.iso"
DEBIAN_ISO_URL=$"http://cdimage.debian.org/debian-cd/7.8.0/amd64/iso-cd/$DEBIAN_ISO"


# Some constants for colored output
red=$(tput setaf 1)
gre=$(tput setaf 2)
rst=$(tput sgr0)

# Check whether necessary files exist
if [ -f $DEBIAN_ISO ]; then
	if [ -f $PRESEED ]; then
		if [ -d $FINISHER ]; then
			echo "$gre""Required files were found$rst"
		else
			echo "$red""ERROR$rst: $FINISHER doesn't exist"
			exit 3
		fi
	else
		echo "$red""ERROR$rst: $PRESEED doesn't exist"
		exit 2
	fi
else
	echo "$red""WARNING$rst: $DEBIAN_ISO doesn't exist"
	echo "Trying to download the image from $DEBIAN_ISO_URL"
	wget $DEBIAN_ISO_URL
fi

# Create working directories
sudo rm -r lts-remaster
mkdir lts-remaster
mkdir lts-remaster/iso-mountpoint
mkdir lts-remaster/cd-remaster

# Mount image in working directory
sudo mount -o loop $DEBIAN_ISO lts-remaster/iso-mountpoint

# Copy image contents to cd-remaster
rsync -avr lts-remaster/iso-mountpoint/ lts-remaster/cd-remaster/

# Unmount image
sudo umount lts-remaster/iso-mountpoint

# Customize remaster with HASDEL stuff
sudo cp -v $PRESEED lts-remaster/cd-remaster/preseed
sudo cp -v $DEBCONFIGFILE lts-remaster/cd-remaster/isolinux
sudo rsync -vr finisher lts-remaster/cd-remaster 

# Create the new iso
cd lts-remaster/cd-remaster
sudo mkisofs -r -V "Prophesy on Debian Install CD" -cache-inodes -J -l -b isolinux/isolinux.bin -c isolinux/boot.cat -no-emul-boot -boot-load-size 4 -boot-info-table -o ../../prophesy_x64.iso .
echo "$gre""Image was created$rst"

# Remove temporary files
cd ../..
sudo rm -r lts-remaster
