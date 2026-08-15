//! Probe whether a running Eclipse/Rodin instance holds the workspace.
//!
//! Eclipse locks `<workspace>/.metadata/.lock` for the lifetime of the
//! instance via Java NIO `FileChannel.tryLock`, which on Unix is a POSIX
//! fcntl record lock. `fcntl(F_GETLK)` observes such a lock without taking
//! it; `flock`-based probes would not see it on Linux. There is no
//! equivalent read-only probe implemented for Windows, so the caller must
//! treat [`LockState::Unknown`] as "attempt the operation and report its
//! failure".

use std::path::Path;

/// Whether the Eclipse workspace at a directory is held by a running instance.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum LockState {
    /// No `.lock` file, or the lock is not held: safe to run headless
    /// operations against the workspace and to launch the GUI.
    Free,
    /// A running instance holds the lock.
    Held,
    /// The platform or an IO error prevented probing.
    Unknown,
}

/// Probe the lock of the Eclipse workspace rooted at `workspace_dir`.
pub fn workspace_lock_state(workspace_dir: &Path) -> LockState {
    let lock_path = workspace_dir.join(".metadata").join(".lock");
    if !lock_path.exists() {
        // Never opened by Eclipse (or not a workspace yet) — nothing running.
        return LockState::Free;
    }
    lock_state_of(&lock_path)
}

#[cfg(unix)]
fn lock_state_of(path: &Path) -> LockState {
    use std::os::fd::AsRawFd;

    let Ok(file) = std::fs::File::open(path) else {
        return LockState::Unknown;
    };
    // Zero-initialise: the flock struct's field order differs across Unixes.
    let mut probe: libc::flock = unsafe { std::mem::zeroed() };
    probe.l_type = libc::F_WRLCK as libc::c_short;
    probe.l_whence = libc::SEEK_SET as libc::c_short;
    let rc = unsafe { libc::fcntl(file.as_raw_fd(), libc::F_GETLK, &mut probe) };
    if rc != 0 {
        return LockState::Unknown;
    }
    if probe.l_type == libc::F_UNLCK as libc::c_short {
        LockState::Free
    } else {
        LockState::Held
    }
}

#[cfg(not(unix))]
fn lock_state_of(_path: &Path) -> LockState {
    LockState::Unknown
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn missing_workspace_is_free() {
        assert_eq!(
            workspace_lock_state(Path::new("/nonexistent/rossi-test-ws")),
            LockState::Free
        );
    }

    #[cfg(unix)]
    #[test]
    fn unlocked_lock_file_is_free() {
        let dir = std::env::temp_dir().join(format!(
            "rossi-lock-test-{}-{}",
            std::process::id(),
            std::time::SystemTime::now()
                .duration_since(std::time::UNIX_EPOCH)
                .unwrap()
                .as_nanos()
        ));
        std::fs::create_dir_all(dir.join(".metadata")).unwrap();
        std::fs::write(dir.join(".metadata").join(".lock"), b"").unwrap();
        assert_eq!(workspace_lock_state(&dir), LockState::Free);
        std::fs::remove_dir_all(&dir).ok();
    }
}
