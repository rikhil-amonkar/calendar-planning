# Requires: z3-solver
# pip install z3-solver

from z3 import *
import json

def solve_itinerary():
    # City indices
    WARSAW, BUDAPEST, PARIS, RIGA = 0, 1, 2, 3
    city_names = {WARSAW: "Warsaw", BUDAPEST: "Budapest", PARIS: "Paris", RIGA: "Riga"}

    # Required total days in each city (including flight overlap days)
    city_days = {
        WARSAW: 2,
        BUDAPEST: 7,
        PARIS: 4,
        RIGA: 7,
    }

    # Direct flight edges (undirected)
    edges = {(WARSAW, BUDAPEST),
             (WARSAW, RIGA),
             (BUDAPEST, PARIS),
             (WARSAW, PARIS),
             (PARIS, RIGA)}
    # Build directed form for convenience
    directed_edges = set()
    for a, b in edges:
        directed_edges.add((a, b))
        directed_edges.add((b, a))

    s = Solver()

    # Order of visiting cities: seq[0] -> seq[1] -> seq[2] -> seq[3]
    seq = [Int(f"seq_{i}") for i in range(4)]
    for v in seq:
        s.add(And(v >= 0, v <= 3))
    s.add(Distinct(seq))

    # Must only move along direct-flight edges
    for i in range(3):
        s.add(Or(*[And(seq[i] == a, seq[i+1] == b) for (a, b) in directed_edges]))

    # Map city variable at position i to its required duration via piecewise If
    def dur_of_city_var(city_var):
        return If(city_var == WARSAW, city_days[WARSAW],
               If(city_var == BUDAPEST, city_days[BUDAPEST],
               If(city_var == PARIS, city_days[PARIS],
                                   city_days[RIGA])))

    dur0 = dur_of_city_var(seq[0])
    dur1 = dur_of_city_var(seq[1])
    dur2 = dur_of_city_var(seq[2])
    dur3 = dur_of_city_var(seq[3])

    # Flight days f1, f2, f3 (days when we switch to the next city; those days count in both cities)
    f1 = Int("f1")
    f2 = Int("f2")
    f3 = Int("f3")

    # f1 = dur0; f2 = f1 + dur1 - 1; f3 = f2 + dur2 - 1
    s.add(f1 == dur0)
    s.add(f2 == f1 + dur1 - 1)
    s.add(f3 == f2 + dur2 - 1)

    # Day ranges for positions:
    # pos0: [1, f1]; pos1: [f1, f2]; pos2: [f2, f3]; pos3: [f3, 17]
    # Valid day bounds
    s.add(And(1 < f1, f1 < f2, f2 < f3, f3 <= 17))

    # The total unique-day length must be 17; with overlaps on f1, f2, f3 built-in, this is ensured
    # by the given city_days sum (20) and 3 flights (overlaps). For robustness, enforce end at 17:
    # end of last segment is fixed at 17 by definition.

    # Constraint: Be in Warsaw on day 1 or day 2 (the annual show).
    # Encode interval overlap with specific days.
    day1, day2 = 1, 2
    def in_range(day, start, end):
        return And(day >= start, day <= end)

    # Start/end per position
    start0, end0 = 1, f1
    start1, end1 = f1, f2
    start2, end2 = f2, f3
    start3, end3 = f3, 17

    in_warsaw_day1 = Or(
        And(seq[0] == WARSAW, in_range(day1, start0, end0)),
        And(seq[1] == WARSAW, in_range(day1, start1, end1)),
        And(seq[2] == WARSAW, in_range(day1, start2, end2)),
        And(seq[3] == WARSAW, in_range(day1, start3, end3))
    )
    in_warsaw_day2 = Or(
        And(seq[0] == WARSAW, in_range(day2, start0, end0)),
        And(seq[1] == WARSAW, in_range(day2, start1, end1)),
        And(seq[2] == WARSAW, in_range(day2, start2, end2)),
        And(seq[3] == WARSAW, in_range(day2, start3, end3))
    )
    s.add(Or(in_warsaw_day1, in_warsaw_day2))

    # Constraint: Be in Riga on at least one day in [11, 17] (wedding window).
    wedding_start, wedding_end = 11, 17
    riga_overlaps_window = Or(
        And(seq[0] == RIGA, end0 >= wedding_start, start0 <= wedding_end),
        And(seq[1] == RIGA, end1 >= wedding_start, start1 <= wedding_end),
        And(seq[2] == RIGA, end2 >= wedding_start, start2 <= wedding_end),
        And(seq[3] == RIGA, end3 >= wedding_start, start3 <= wedding_end)
    )
    s.add(riga_overlaps_window)

    if s.check() != sat:
        raise RuntimeError("No feasible itinerary found under the given constraints.")

    m = s.model()

    # Extract sequence and flight days
    seq_val = [m.evaluate(seq[i]).as_long() for i in range(4)]
    f1_val = m.evaluate(f1).as_long()
    f2_val = m.evaluate(f2).as_long()
    f3_val = m.evaluate(f3).as_long()

    # Build day-to-cities mapping based on intervals with overlaps on flight days
    # pos0: [1, f1], pos1: [f1, f2], pos2: [f2, f3], pos3: [f3, 17]
    itinerary = []
    for d in range(1, 18):
        cities_today = []
        if 1 <= d <= f1_val:
            cities_today.append(city_names[seq_val[0]])
        if f1_val <= d <= f2_val:
            c = city_names[seq_val[1]]
            if c not in cities_today:
                cities_today.append(c)
        if f2_val <= d <= f3_val:
            c = city_names[seq_val[2]]
            if c not in cities_today:
                cities_today.append(c)
        if f3_val <= d <= 17:
            c = city_names[seq_val[3]]
            if c not in cities_today:
                cities_today.append(c)
        itinerary.append({"day": d, "cities": cities_today})

    # Output as JSON with the required schema
    print(json.dumps({"itinerary": itinerary}, ensure_ascii=False, indent=2))


if __name__ == "__main__":
    solve_itinerary()