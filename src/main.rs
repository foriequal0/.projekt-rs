use std::fmt::{Debug, Display, Formatter};
use std::io::{stdin, BufRead, BufReader};
use std::ops::BitOr;

use anyhow::*;

fn main() -> Result<()> {
    let (xz, yz) = get_plains()?;
    let mut cube = Cube::new(xz.x, yz.x, xz.z);
    let xz_columns: Vec<(u8, u8)> = cube.project_xz().diff(&xz).collect();

    for (x, z) in xz_columns {
        for bitmap in bitmaps(cube.y) {
            for y in bitmap {
                if !cube.project_to_xz(x, z) || !cube.project_to_yz(y, z) {
                    cube.set(x, y, z, yz.get(y, z));
                }
            }
        }
    }

    assert_eq!(cube.project_xz(), xz);
    assert_eq!(cube.project_yz(), yz);

    println!("{}", cube);
    Ok(())
}

fn bitmaps(width: u8) -> impl Iterator<Item = impl Iterator<Item = u8>> {
    (1..(1 << width)).map(move |bitmap| {
        (0..width).filter(move |&offset| {
            bitmap >> offset & 1 == 1
        })
    })
}

const COORDINATE: &str = "
      Y (0,Y,0)
       .-|-.
 O .-'   |   '-. (X,Y,0)
  |  YZ  |  XZ  |
  |      |      |
  |    .-'-(0,Y,Z)
  |.-'       '-.|
Z(0,0,Z)     .-' (X,Y,Z)
       '-.-'
      X (X,0,Z)
";
#[derive(Eq, PartialEq, Hash, Clone)]
struct Cube {
    bitmap: Vec<bool>,
    x: u8,
    y: u8,
    z: u8,
}

impl Cube {
    fn new(x: u8, y: u8, z: u8) -> Self {
        Self {
            bitmap: vec![false; x as usize * y as usize * z as usize],
            x,
            y,
            z,
        }
    }

    fn index(&self, x: u8, y: u8, z: u8) -> usize {
        x as usize * (self.y as usize * self.z as usize) + y as usize * self.z as usize + z as usize
    }

    fn get(&self, x: u8, y: u8, z: u8) -> bool {
        self.bitmap[self.index(x, y, z)]
    }

    fn set(&mut self, x: u8, y: u8, z: u8, value: bool) {
        let value = self.get(x, y, z) || value;
        let index = self.index(x, y, z);
        self.bitmap[index] = value;
    }

    fn project_xz(&self) -> Plain {
        let mut plain = Plain::new(self.x, self.z);
        for x in 0..self.x {
            for y in 0..self.y {
                for z in 0..self.z {
                    plain.set(x, z, self.get(x, y, z));
                }
            }
        }
        plain
    }

    fn project_to_xz(&self, x: u8, z: u8) -> bool {
        (0..self.y).any(|y| self.get(x, y ,z))
    }

    fn project_yz(&self) -> Plain {
        let mut plain = Plain::new(self.y, self.z);
        for x in 0..self.x {
            for y in 0..self.y {
                for z in 0..self.z {
                    plain.set(y, z, self.get(x, y, z));
                }
            }
        }
        plain
    }

    fn project_to_yz(&self, y: u8, z: u8) -> bool {
        (0..self.x).any(|x| self.get(x, y ,z))
    }
}

impl BitOr for Cube {
    type Output = Cube;

    fn bitor(self, rhs: Self) -> Self::Output {
        debug_assert_eq!(self.x, rhs.x);
        debug_assert_eq!(self.y, rhs.y);
        debug_assert_eq!(self.z, rhs.z);

        Self {
            bitmap: self.bitmap.iter().copied().zip(rhs.bitmap.iter().copied()).map(|(a, b)| a || b).collect(),
            ..self
        }
    }
}

impl Display for Cube {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        writeln!(f, "top")?;
        for z in 0..self.z {
            writeln!(f, " y")?;
            for y in (0..self.y).rev() {
                if y == self.y - 1 {
                    write!(f, " ^")?
                } else if (y + 1) % 5 == 0 {
                    write!(f, " +")?;
                } else {
                    write!(f, " |")?;
                }

                for x in 0..self.x {
                    let value = self.get(x, y, z);
                    if value {
                        write!(f, "#")?;
                    } else if (x + 1) % 5 == 0 && (y + 1) % 5 == 0 {
                        write!(f, "+")?;
                    } else {
                        // Unicode middle dot "·"
                        write!(f, "\u{b7}")?;
                    }
                }
                writeln!(f)?;
            }

            write!(f, "{:2}", z)?;
            for x in 0..(self.x-1) {
                if (x + 1) % 5 == 0 {
                    write!(f, "+")?;
                } else {
                    write!(f, "-")?;
                }
            }
            writeln!(f, "> x")?;
        }
        writeln!(f, "bottom")?;
        Ok(())
    }
}

#[derive(Eq, PartialEq, Clone)]
struct Plain {
    bitmap: Vec<bool>,
    /// an axis perpendicular to the projection axis
    x: u8,
    /// Z axis of a cube
    z: u8,
}

impl Plain {
    fn new(x: u8, z: u8) -> Self {
        Self {
            bitmap: vec![false; x as usize * z as usize],
            x,
            z,
        }
    }

    fn from_lines(lines: &[String]) -> Result<Self, &'static str> {
        if lines.is_empty() {
            return Err("empty input");
        }
        let height = lines.len();
        let width = lines[0].len();
        if lines.iter().any(|line| line.len() != width) {
            return Err("irregular line");
        }
        let mut plain = Plain::new(width as u8, height as u8);
        for (y, line) in lines.iter().enumerate() {
            for (x, char) in line.chars().enumerate() {
                match char {
                    '#' | '*' => plain.set(x as u8, y as u8, true),
                    '_' | ' ' | '.' => plain.set(x as u8, y as u8, false),
                    _ => return Err("invalid char"),
                }
            }
        }
        Ok(plain)
    }

    fn index(&self, x: u8, z: u8) -> usize {
        x as usize * self.z as usize + z as usize
    }

    fn get(&self, x: u8, z: u8) -> bool {
        let index = self.index(x, z);
        self.bitmap[index]
    }

    fn set(&mut self, x: u8, z: u8, value: bool) {
        let value = self.get(x, z) || value;
        let index = self.index(x, z);
        self.bitmap[index] = value;
    }

    fn diff<'a>(&'a self, other: &'a Plain) -> impl Iterator<Item = (u8, u8)> + 'a {
        debug_assert_eq!(self.x, other.x);
        debug_assert_eq!(self.z, other.z);

        (0..self.x)
            .flat_map(move |x| (0..self.z).map(move |z| (x, z)))
            .filter(move |&(x, z)| self.get(x, z) != other.get(x, z))
    }
}

impl Display for Plain {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        for z in 0..self.z {
            for x in 0..self.x {
                let value = self.get(x, z);
                if value {
                    write!(f, "#")?;
                } else {
                    write!(f, ".")?;
                }
            }
            writeln!(f)?;
        }
        Ok(())
    }
}

impl Debug for Plain {
    fn fmt(&self, f: &mut Formatter<'_>) -> std::fmt::Result {
        Display::fmt(self, f)
    }
}

fn get_plains() -> Result<(Plain, Plain)> {
    println!("{}", COORDINATE);

    let mut read_lines = BufReader::new(stdin()).lines();
    println!("Put XZ plain (# for black, _ for white, double return to end)");
    let xz = {
        let mut lines = Vec::new();
        loop {
            match read_lines.next() {
                Some(Ok(line)) => {
                    if line.chars().count() == 0 {
                        break Plain::from_lines(&lines)
                            .map_err(|err| anyhow!(err))
                            .context("Error while reading XZ plain")?;
                    } else {
                        lines.push(line);
                    }
                }
                Some(Err(err)) => return Err(err.into()),
                None => return Err(anyhow!("Unexpected EOF while reading XZ plain")),
            }
        }
    };

    println!("Put YZ plain (# for black, _ for white, double return to end)");
    let yz = {
        let mut lines = Vec::new();
        loop {
            match read_lines.next() {
                Some(Ok(line)) => {
                    if line.chars().all(char::is_whitespace) {
                        break Plain::from_lines(&lines)
                            .map_err(|err| anyhow!(err))
                            .context("Error while reading YZ plain")?;
                    } else {
                        lines.push(line);
                    }
                }
                Some(Err(err)) => return Err(err.into()),
                None => return Err(anyhow!("Unexpected EOF while reading YZ plain")),
            }
        }
    };

    if xz.z != yz.z {
        return Err(anyhow!("Height mismatch"));
    }

    Ok((xz, yz))
}
