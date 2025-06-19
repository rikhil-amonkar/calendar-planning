itinerary = [
    # Week 1
    "M7",  # Day 1: Sunday (g)
    "P1",  # Day 2: Monday (c)
    "R3",  # Day 3: Tuesday (d)
    "P4",  # Day 4: Wednesday
    "R1",  # Day 5: Thursday
    "P5",  # Day 6: Friday
    "M1",  # Day 7: Saturday (partial i: Saturday but not third)
    
    # Week 2
    "P2",  # Day 8: Sunday (after museum)
    "R4",  # Day 9: Monday
    "M3",  # Day 10: Tuesday (e: different weekday than M1)
    "M4",  # Day 11: Wednesday (j: middle day museum)
    "P3",  # Day 12: Thursday (f: same weekday as R1)
    "R7",  # Day 13: Friday (h: before M4 placement)
    "M5",  # Day 14: Saturday (after park)
    
    # Week 3
    "P6",  # Day 15: Sunday (after museum)
    "R5",  # Day 16: Monday
    "M2",  # Day 17: Tuesday
    "P7",  # Day 18: Wednesday (after museum)
    "R6",  # Day 19: Thursday
    "M6",  # Day 20: Friday
    "P7"   # Day 21: Saturday (b: last day)
]

# Print the itinerary
for activity in itinerary:
    print(activity)