from z3 import *

# Create a solver instance
s = Solver()

# Helper: time is measured in minutes after midnight.
# Our starting point: arrive at Russian Hill at 9:00 (i.e. 9*60 = 540 minutes)

start_time = 540  # 9:00 AM

# Define meeting start time variables for the 8 chosen friends
S_william   = Int('S_william')   # meeting at Presidio, friend: William
S_kimberly  = Int('S_kimberly')  # meeting at Alamo Square, friend: Kimberly
S_david     = Int('S_david')     # meeting at Sunset District, friend: David
S_joshua    = Int('S_joshua')    # meeting at Financial District, friend: Joshua
S_patricia  = Int('S_patricia')  # meeting at Nob Hill, friend: Patricia
S_ronald    = Int('S_ronald')    # meeting at Embarcadero, friend: Ronald
S_charles   = Int('S_charles')   # meeting at Richmond District, friend: Charles
S_kenneth   = Int('S_kenneth')   # meeting at Union Square, friend: Kenneth

# Durations in minutes (must meet at least the minimum duration)
dur_william   = 60    # William: 60 min; availability [7:00, 12:45]
dur_kimberly  = 105   # Kimberly: 105 min; availability [9:00, 14:30]
dur_david     = 15    # David: 15 min; availability [9:15, 22:00]
dur_joshua    = 90    # Joshua: 90 min; availability [14:30, 17:15]
dur_patricia  = 120   # Patricia: 120 min; availability [15:00, 19:15]
dur_ronald    = 30    # Ronald: 30 min; availability [18:15, 20:45]
dur_charles   = 15    # Charles: 15 min; availability [17:15, 21:00]
dur_kenneth   = 15    # Kenneth: 15 min; availability [21:15, 21:45]

# Availability windows (in minutes after midnight)
# William: 7:00  = 420, 12:45 = 765
avail_william  = (420, 765)
# Kimberly: 9:00 = 540, 14:30 = 870
avail_kimberly = (540, 870)
# David: 9:15 = 555, 22:00 = 1320
avail_david    = (555, 1320)
# Joshua: 14:30 = 870, 17:15 = 1035
avail_joshua   = (870, 1035)
# Patricia: 15:00 = 900, 19:15 = 1155
avail_patricia = (900, 1155)
# Ronald: 18:15 = 1095, 20:45 = 1245
avail_ronald   = (1095, 1245)
# Charles: 17:15 = 1035, 21:00 = 1260
avail_charles  = (1035, 1260)
# Kenneth: 21:15 = 1275, 21:45 = 1305
avail_kenneth  = (1275, 1305)

# Travel times between meeting locations (in minutes)
# You begin at Russian Hill.
#  Russian Hill -> Presidio = 14.
#  Presidio -> Alamo Square = 19.
#  Alamo Square -> Sunset District = 16.
#  Sunset District -> Financial District = 30.
#  Financial District -> Nob Hill = 8.
#  Nob Hill -> Embarcadero = 9.
#  Embarcadero -> Richmond District = 21.
#  Richmond District -> Union Square = 21.

# William (Presidio): Must be reached from Russian Hill.
s.add(S_william >= start_time + 14)
s.add(S_william >= avail_william[0])
s.add(S_william + dur_william <= avail_william[1])

# Kimberly (Alamo Square): after William plus travel (Presidio -> Alamo Square = 19)
s.add(S_kimberly >= S_william + dur_william + 19)
s.add(S_kimberly >= avail_kimberly[0])
s.add(S_kimberly + dur_kimberly <= avail_kimberly[1])

# David (Sunset District): after Kimberly plus travel (Alamo Square -> Sunset District = 16)
s.add(S_david >= S_kimberly + dur_kimberly + 16)
s.add(S_david >= avail_david[0])
s.add(S_david + dur_david <= avail_david[1])

# Joshua (Financial District): after David plus travel (Sunset District -> Financial District = 30)
s.add(S_joshua >= S_david + dur_david + 30)
# Also Joshua’s own window forces start >= 14:30 (870).
s.add(S_joshua >= avail_joshua[0])
s.add(S_joshua + dur_joshua <= avail_joshua[1])

# Patricia (Nob Hill): after Joshua plus travel (Financial District -> Nob Hill = 8)
s.add(S_patricia >= S_joshua + dur_joshua + 8)
s.add(S_patricia >= avail_patricia[0])
s.add(S_patricia + dur_patricia <= avail_patricia[1])

# Ronald (Embarcadero): after Patricia plus travel (Nob Hill -> Embarcadero = 9)
s.add(S_ronald >= S_patricia + dur_patricia + 9)
s.add(S_ronald >= avail_ronald[0])
s.add(S_ronald + dur_ronald <= avail_ronald[1])

# Charles (Richmond District): after Ronald plus travel (Embarcadero -> Richmond District = 21)
s.add(S_charles >= S_ronald + dur_ronald + 21)
s.add(S_charles >= avail_charles[0])
s.add(S_charles + dur_charles <= avail_charles[1])

# Kenneth (Union Square): after Charles plus travel (Richmond District -> Union Square = 21)
s.add(S_kenneth >= S_charles + dur_charles + 21)
s.add(S_kenneth >= avail_kenneth[0])
s.add(S_kenneth + dur_kenneth <= avail_kenneth[1])

# At this point the constraints force a schedule.
# (The above ordering – William, Kimberly, David, Joshua, Patricia, Ronald, Charles, Kenneth – is our chosen optimal chain.)

if s.check() == sat:
    m = s.model()
    # Helper to convert minutes to HH:MM format
    def to_time(minutes):
        h = minutes // 60
        mnt = minutes % 60
        return f"{h:02d}:{mnt:02d}"
    itinerary = [
        {"action": "meet", "person": "William",  "start_time": to_time(m[S_william].as_long()),  "end_time": to_time(m[S_william].as_long()  + dur_william)},
        {"action": "meet", "person": "Kimberly", "start_time": to_time(m[S_kimberly].as_long()), "end_time": to_time(m[S_kimberly].as_long() + dur_kimberly)},
        {"action": "meet", "person": "David",    "start_time": to_time(m[S_david].as_long()),    "end_time": to_time(m[S_david].as_long()    + dur_david)},
        {"action": "meet", "person": "Joshua",   "start_time": to_time(m[S_joshua].as_long()),   "end_time": to_time(m[S_joshua].as_long()   + dur_joshua)},
        {"action": "meet", "person": "Patricia", "start_time": to_time(m[S_patricia].as_long()), "end_time": to_time(m[S_patricia].as_long() + dur_patricia)},
        {"action": "meet", "person": "Ronald",   "start_time": to_time(m[S_ronald].as_long()),   "end_time": to_time(m[S_ronald].as_long()   + dur_ronald)},
        {"action": "meet", "person": "Charles",  "start_time": to_time(m[S_charles].as_long()),  "end_time": to_time(m[S_charles].as_long()  + dur_charles)},
        {"action": "meet", "person": "Kenneth",  "start_time": to_time(m[S_kenneth].as_long()),  "end_time": to_time(m[S_kenneth].as_long()  + dur_kenneth)}
    ]
    
    import json
    print(json.dumps({"itinerary": itinerary}, indent=4))
else:
    print("No solution found")