from z3 import *

# Define start times for each friend (Joseph's start is fixed)
Kevin_start = Int('Kevin_start')
Kimberly_start = Int('Kimberly_start')
Thomas_start = Int('Thomas_start')
Joseph_start = 1110  # 6:30 PM in minutes since midnight

s = Solver()

# Friend constraints
s.add(Kevin_start >= 540 + 17)       # Earliest 9:17 AM (557)
s.add(Kevin_start + 75 <= 1290)      # Latest end by 9:30 PM
s.add(Kimberly_start >= 540 + 24)    # Earliest 9:24 AM (564)
s.add(Kimberly_start + 30 <= 750)    # Latest end by 12:30 PM
s.add(Thomas_start >= 1155 + 23)     # Earliest 19:38 (1178) due to Joseph's travel
s.add(Thomas_start + 45 <= 1305)     # Latest end by 9:45 PM

# Travel times between locations (Sunset=0, Alamo=1, Russian=2, Presidio=3, Financial=4)
def travel_time(from_loc, to_loc):
    tt = {
        (0,1):17, (0,2):24, (0,3):16, (0,4):30,
        (1,0):16, (1,2):13, (1,3):18, (1,4):17,
        (2,0):23, (2,1):15, (2,3):14, (2,4):11,
        (3,0):15, (3,1):18, (3,2):14, (3,4):23,
        (4,0):31, (4,1):17, (4,2):10, (4,3):22,
    }
    return tt[(from_loc, to_loc)]

# Pairwise scheduling constraints
# Kevin <-> Kimberly
s.add(Or(
    Kevin_start + 75 + travel_time(1,2) <= Kimberly_start,
    Kimberly_start + 30 + travel_time(2,1) <= Kevin_start
))
# Kevin <-> Joseph
s.add(Or(
    Kevin_start + 75 + travel_time(1,3) <= Joseph_start,
    Joseph_start + 45 + travel_time(3,1) <= Kevin_start
))
# Kevin <-> Thomas
s.add(Or(
    Kevin_start + 75 + travel_time(1,4) <= Thomas_start,
    Thomas_start + 45 + travel_time(4,1) <= Kevin_start
))
# Kimberly <-> Joseph
s.add(Or(
    Kimberly_start + 30 + travel_time(2,3) <= Joseph_start,
    Joseph_start + 45 + travel_time(3,2) <= Kimberly_start
))
# Kimberly <-> Thomas
s.add(Or(
    Kimberly_start + 30 + travel_time(2,4) <= Thomas_start,
    Thomas_start + 45 + travel_time(4,2) <= Kimberly_start
))
# Joseph <-> Thomas (Joseph's end is 1155)
s.add(Or(
    1155 + travel_time(3,4) <= Thomas_start,
    Thomas_start + 45 + travel_time(4,3) <= Joseph_start
))

# Ensure one friend is first with travel from Sunset
is_first = [Bool(f'is_first_{n}') for n in ['Kev','Kim','Jos','Tho']]
s.add(Sum([If(b,1,0) for b in is_first]) == 1)
s.add(Implies(is_first[0], Kevin_start >= 540+17))
s.add(Implies(is_first[1], Kimberly_start >= 540+24))
s.add(Implies(is_first[2], Joseph_start >= 540+16))  # Always true
s.add(Implies(is_first[3], Thomas_start >= 540+30))  # Always true

if s.check() == sat:
    m = s.model()
    print("Optimal Schedule:")
    print(f"Kevin: {m[Kevin_start].as_long()//60:02d}:{m[Kevin_start].as_long()%60:02d} - {(m[Kevin_start].as_long()+75)//60:02d}:{(m[Kevin_start].as_long()+75)%60:02d}")
    print(f"Kimberly: {m[Kimberly_start].as_long()//60:02d}:{m[Kimberly_start].as_long()%60:02d} - {(m[Kimberly_start].as_long()+30)//60:02d}:{(m[Kimberly_start].as_long()+30)%60:02d}")
    print(f"Joseph: 18:30 - 19:15")  # Fixed
    print(f"Thomas: {m[Thomas_start].as_long()//60:02d}:{m[Thomas_start].as_long()%60:02d} - {(m[Thomas_start].as_long()+45)//60:02d}:{(m[Thomas_start].as_long()+45)%60:02d}")
else:
    print("No valid schedule found.")