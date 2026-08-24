{
  description = "@aufbau/syntax development environment";

  inputs = {
    nixpkgs.url = "github:NixOS/nixpkgs/nixos-unstable";
    systems.url = "github:nix-systems/default";
  };

  outputs =
    {
      self,
      nixpkgs,
      systems,
    }:
    let
      eachSystem = nixpkgs.lib.genAttrs (import systems);
    in
    {
      devShells = eachSystem (
        system:
        let
          pkgs = import nixpkgs {
            inherit system;
          };
        in
        {
          default = pkgs.mkShell {
            packages = with pkgs; [
              bashInteractive

              # Bun runs the suite and the tooling; Node runs the release
              # scripts and the smoke test, which is the whole point of that
              # test — the published artifact must load outside Bun. CI pins
              # Node 24, so this shell does too.
              bun
              nodejs_24

              git
              gh
              ripgrep
              fd
              jq

              nil
              nixfmt
              typescript-language-server
            ];
          };
        }
      );
    };
}
