package cxcore

import (
	"fmt"
	"io/ioutil"
	"os"
)

var workingDir string
var logFile bool

// CXSetWorkingDir ...
func CXSetWorkingDir(dir string) {
	workingDir = dir
}

// CXLogFile ...
func CXLogFile(enable bool) {
	logFile = enable
}

// CXOpenFile ...
func CXOpenFile(path string) (*os.File, error) {
	if logFile {
		fmt.Printf("Opening file : '%s', '%s'\n", workingDir, path)
	}

	file, err := os.Open(fmt.Sprintf("%s%s", workingDir, path))
	if logFile && err != nil {
		fmt.Printf("Failed to open file : '%s', '%s', err '%v'\n", workingDir, path, err)
	}
	return file, err
}

// CXCreateFile ...
func CXCreateFile(path string) (*os.File, error) {
	if logFile {
		fmt.Printf("Creating file : '%s', '%s'\n", workingDir, path)
	}

	file, err := os.Create(fmt.Sprintf("%s%s", workingDir, path))
	if logFile && err != nil {
		fmt.Printf("Failed to create file : '%s', '%s', err '%v'\n", workingDir, path, err)
	}

	return file, err
}

// CXRemoveFile ...
func CXRemoveFile(path string) error {
	if logFile {
		fmt.Printf("Removing file : '%s', '%s'\n", workingDir, path)
	}

	err := os.Remove(fmt.Sprintf("%s%s", workingDir, path))

	if logFile && err != nil {
		fmt.Printf("Failed to remove file : '%s', '%s', err '%v'\n", workingDir, path, err)
	}

	return err
}

// CXReadFile ...
func CXReadFile(path string) ([]byte, error) {
	if logFile {
		fmt.Printf("Reading file : '%s', '%s'\n", workingDir, path)
	}

	bytes, err := ioutil.ReadFile(fmt.Sprintf("%s%s", workingDir, path))

	if logFile && err != nil {
		fmt.Printf("Failed to read file : '%s', '%s', err '%v'\n", workingDir, path, err)
	}

	return bytes, err
}

// CXStatFile ...
func CXStatFile(path string) (os.FileInfo, error) {
	if logFile {
		fmt.Printf("Stating file : '%s', '%s'\n", workingDir, path)
	}

	fileInfo, err := os.Stat(fmt.Sprintf("%s%s", workingDir, path))

	if logFile && err != nil {
		fmt.Printf("Failed to stat file : '%s', '%s', err '%v'\n", workingDir, path, err)
	}

	return fileInfo, err
}

// CXMkdirAll ...
func CXMkdirAll(path string, perm os.FileMode) error {
	if logFile {
		fmt.Printf("Creating dir : '%s'\n", path)
	}

	err := os.MkdirAll(fmt.Sprintf("%s%s", workingDir, path), perm)

	if logFile && err != nil {
		fmt.Printf("Failed to create dir : '%s', '%s', err '%v'\n", workingDir, path, err)
	}

	return err
}
