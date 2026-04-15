/- Copyright (c) Heather Macbeth, 2022.  All rights reserved. -/
import Library.Basic

math2001_init


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw [ha]
    _ = 8 * (-3 * a + 2 * n) := by ring


example {n : ℤ} (hn : 8 ∣ 5 * n) : 8 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -3 * a + 2 * n
  calc
    n = -3 * (5 * n) + 16 * n := by ring
    _ = -3 * (8 * a) + 16 * n := by rw[ha]
    _ = -24 * a + 16 * n := by ring
    _ = 8 * (-3 * a + 2 * n) := by ring

example {n : ℤ} (h1 : 5 ∣ 3 * n) : 5 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  use -3 * a + 2 * n
  calc
    n = -3 * (3 * n) + 5 * (2 * n) := by ring
    _ = -3 * (5 * a) + 5 * (2 * n) := by rw[ha]
    _ = -15 * a + 5 * (2 * n) := by ring
    _ = 5 * (-3 * a + 2 * n) := by ring

example {m : ℤ} (h1 : 8 ∣ m) (h2 : 5 ∣ m) : 40 ∣ m := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use -3 * a + 2 * b
  calc
    m = -15 * m + 16 * m := by ring
    _ = -15 * (8 * a) + 16 * m := by rw [ha]
    _ = -15 * (8 * a) + 16 * (5 * b) := by rw [hb]
    _ = 40 * (-3 * a + 2 * b) := by ring

/-! # Exercises -/


example {n : ℤ} (hn : 6 ∣ 11 * n) : 6 ∣ n := by
  obtain ⟨a, ha⟩ := hn
  use -a + 2 * n
  calc
    n = -1 * (11 * n) + 12 * n := by ring
    _ = -1 * (6 * a) + 12 * n := by rw[ha]
    _ = 6 * (-a + 2 * n) := by ring

example {a : ℤ} (ha : 7 ∣ 5 * a) : 7 ∣ a := by
  obtain ⟨x, hx⟩ := ha
  use 3 * x - 2 * a
  calc
    a = 3 * (5 * a) - 14 * a := by ring
    _ = 3 * (7 * x) - 14 * a := by rw[hx]
    _ = 7 * (3 * x - 2 * a) := by ring


example {n : ℤ} (h1 : 7 ∣ n) (h2 : 9 ∣ n) : 63 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use 4 * b - 3 * a
  calc
    n = 7 * (4 * n) - 9 * (3 * (n)) := by ring
    _ = 7 * (4 * (9 * b)) - 9 * (3 * n) := by rw[hb]
    _ = 7 * (4 * (9 * b)) - 9 * (3 * (7 * a)) := by rw[ha]
    _ = 252 * b - 189 * a := by ring
    _ = 63 * (4 * b  - 3 * a) := by ring

example {n : ℤ} (h1 : 5 ∣ n) (h2 : 13 ∣ n) : 65 ∣ n := by
  obtain ⟨a, ha⟩ := h1
  obtain ⟨b, hb⟩ := h2
  use 2 * a - 5 * b
  calc
    n = 13 * (2 * n) - 5 * (5 * n) := by ring
    _ = 13 * (2 * (5 * a)) - 5 * (5 * n) := by rw[ha]
    _ = 13 * (2 * (5 * a)) - 5 * (5 * (13 * b)) := by rw[hb]
    _ = 130 * a - 325 * b := by ring
    _ = 65 * (2 * a - 5 * b) := by ring
