const std = @import("std");

pub fn build(b: *std.Build) void {
    const optimize = b.standardOptimizeOption(.{});
    const target = b.standardTargetOptions(.{});

    const exe = b.addExecutable(.{
        .name = "compiler",
        .root_module = b.createModule(.{
            .root_source_file = b.path("src/linux.zig"),
            .target = target,
            .optimize = optimize,
        }),
    });
    b.installArtifact(exe);

    const run_cmd = b.addRunArtifact(exe);
    const compile = b.step("run", "compile test file");
    compile.dependOn(&run_cmd.step);
}
