package main

import (
	"fmt"
	"log"
	"net/http"
	"os"
)

func main() {
	// Check for a command-line argument for the path
	if len(os.Args) < 2 {
		fmt.Println("Usage: go run main.go <path>")
		os.Exit(1)
	}

	path := os.Args[1]

	// Create a file server handler
	fileServer := http.FileServer(http.Dir(path))

	// Use the file server handler for the root path
	http.Handle("/", fileServer)

	// Define the addr for the server
	addr := "127.0.0.1:9080"

	// Start the server
	log.Printf("Serving %s on HTTP port %s\n", path, addr)
	if err := http.ListenAndServe(addr, nil); err != nil {
		log.Fatalf("Could not start server: %s\n", err)
	}
}
