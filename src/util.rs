/// Looks up a username, given a uid
pub fn lookup_username(uid: u32) -> Result<String, String> {
    use libc::{getpwuid_r, passwd, sysconf, _SC_GETPW_R_SIZE_MAX};
    use std::ffi::CStr;
    use std::mem::zeroed;

    let buf_size = match unsafe { sysconf(_SC_GETPW_R_SIZE_MAX) } {
        x if x <= 0 => {
            // make some something that we think will be big enough
            1024
        }
        x => x as usize,
    };

    let mut buf = vec![0; buf_size];
    let mut pwd: passwd = unsafe { zeroed() };

    let mut ptr = 0 as *mut passwd;

    if unsafe { getpwuid_r(uid, &mut pwd, buf.as_mut_ptr(), buf_size, &mut ptr) } == 0 {
        if !ptr.is_null() {
            let name = unsafe { CStr::from_ptr(pwd.pw_name) };
            return Ok(name.to_string_lossy().into_owned());
        }
    }

    Err(format!("Unable to find username for uid {}", uid))
}

pub fn lookup_uid(wanted_username: &str) -> Result<u32, String> {
    use libc::{getpwnam_r, passwd, sysconf, _SC_GETPW_R_SIZE_MAX};
    use std::mem::zeroed;

    let buf_size = match unsafe { sysconf(_SC_GETPW_R_SIZE_MAX) } {
        x if x <= 0 => {
            // make some something that we think will be big enough
            1024
        }
        x => x as usize,
    };

    let mut buf = vec![0; buf_size];
    let mut pwd: passwd = unsafe { zeroed() };
    let username = ::std::ffi::CString::new(wanted_username.to_string()).unwrap();

    let mut ptr = 0 as *mut passwd;

    if unsafe {
        getpwnam_r(
            username.as_ptr() as *const i8,
            &mut pwd,
            buf.as_mut_ptr(),
            buf_size,
            &mut ptr,
        )
    } == 0
    {
        if !ptr.is_null() {
            return Ok(pwd.pw_uid);
        }
    }

    Err(format!(
        "Unable to find UID for username {:?}",
        wanted_username
    ))
}

#[cfg(test)]
mod test {
    use super::*;

    #[cfg(unix)]
    #[test]
    fn test_lookup_uid() {
        use libc;

        let current_username = unsafe {
            let u = ::libc::getlogin();
            ::std::ffi::CStr::from_ptr(u)
        };

        let r = lookup_uid(&current_username.to_string_lossy()).unwrap();
        println!("{:?}", r);

        assert_eq!(r as u32, unsafe { ::libc::getuid() });
    }

    #[cfg(unix)]
    #[test]
    fn test_lookup_username() {
        let uid = unsafe { ::libc::getuid() };
        let username = lookup_username(uid).unwrap();

        let current_username = unsafe {
            let u = ::libc::getlogin();
            ::std::ffi::CStr::from_ptr(u)
        };

        assert_eq!(username.as_str(), current_username.to_str().unwrap());
    }

}
