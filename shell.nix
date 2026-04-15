#!/usr/bin/env nix-shell
{ pkgs ? import <nixpkgs> { } }:
pkgs.mkShell {
  buildInputs = with pkgs; [
  ];

  # shellHook = "exec ${pkgs.lib.getExe pkgs.fish}";
  shellHook = "exec ${pkgs.lib.getExe pkgs.vscode-fhs}";
}
