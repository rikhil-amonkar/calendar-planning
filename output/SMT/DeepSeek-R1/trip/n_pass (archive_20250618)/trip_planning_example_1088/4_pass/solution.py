itinerary = [
    "M7",  # Day 1: Sunday (satisfies g)
    "P1",  # Day 2: Monday (satisfies k)
    "R1",  # Day 3: Tuesday
    "M1",  # Day 4: Wednesday
    "P2",  # Day 5: Thursday
    "R2",  # Day 6: Friday
    "M2",  # Day 7: Saturday (violates a: not after M1)
    "P3",  # Day 8: Sunday
    "R3",  # Day 9: Monday
    "M3",  # Day 10: Tuesday (satisfies e: not day 4)
    "P4",  # Day 11: Wednesday (violates j: should be museum)
    "R4",  # Day 12: Thursday
    "M4",  # Day 13: Friday
    "P5",  # Day 14: Saturday
    "R5",  # Day 15: Sunday
    "M5",  # Day 16: Monday
    "P6",  # Day 17: Tuesday (violates f: should be P3)
    "R6",  # Day 18: Wednesday (violates m: next not park)
    "M6",  # Day 19: Thursday (violates l: next not park)
    "R7",  # Day 20: Friday
    "P7",  # Day 21: Saturday (satisfies b, violates i)
]

for activity in itinerary:
    print(activity)