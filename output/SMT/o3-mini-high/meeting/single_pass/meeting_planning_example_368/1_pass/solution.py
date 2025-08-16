from z3 import *

# Create a solver instance
s = Solver()

# Represent times as minutes from midnight.
# For example, 09:00 is 9*60 = 540.
arrival_time = 9 * 60  # 540, arriving at Bayview at 09:00

# Friend availability windows (in minutes from midnight):
# Joseph: available at Russian Hill from 08:30 to 19:15, needs at least 60 minutes.
joseph_avail_start = 8 * 60 + 30   # 8:30 = 510
joseph_avail_end   = 19 * 60 + 15    # 19:15 = 1155

# Nancy: available at Alamo Square from 11:00 to 16:00, needs at least 90 minutes.
nancy_avail_start = 11 * 60          # 11:00 = 660
nancy_avail_end   = 16 * 60          # 16:00 = 960

# Jeffrey: available at Financial District from 10:30 to 15:45, needs at least 45 minutes.
jeffrey_avail_start = 10 * 60 + 30   # 10:30 = 630
jeffrey_avail_end   = 15 * 60 + 45   # 15:45 = 945

# Jason: available at North Beach from 16:45 to 21:45, needs at least 15 minutes.
jason_avail_start = 16 * 60 + 45     # 16:45 = 1005
jason_avail_end   = 21 * 60 + 45     # 21:45 = 1305

# Travel times (in minutes) between locations:
# (From, To): time in minutes.
travel_times = {
    ("Bayview", "Russian Hill"): 23,
    ("Bayview", "Alamo Square"): 16,
    ("Bayview", "North Beach"): 21,
    ("Bayview", "Financial District"): 19,
    
    ("Russian Hill", "Bayview"): 23,
    ("Russian Hill", "Alamo Square"): 15,
    ("Russian Hill", "North Beach"): 5,
    ("Russian Hill", "Financial District"): 11,
    
    ("Alamo Square", "Bayview"): 16,
    ("Alamo Square", "Russian Hill"): 13,
    ("Alamo Square", "North Beach"): 15,
    ("Alamo Square", "Financial District"): 17,
    
    ("North Beach", "Bayview"): 22,
    ("North Beach", "Russian Hill"): 4,
    ("North Beach", "Alamo Square"): 16,
    ("North Beach", "Financial District"): 8,
    
    ("Financial District", "Bayview"): 19,
    ("Financial District", "Russian Hill"): 10,
    ("Financial District", "Alamo Square"): 17,
    ("Financial District", "North Beach"): 7
}

# For each friend, define integer variables for the meeting start and end times.
Joseph_start = Int("Joseph_start")
Joseph_end   = Int("Joseph_end")
Jeffrey_start = Int("Jeffrey_start")
Jeffrey_end   = Int("Jeffrey_end")
Nancy_start   = Int("Nancy_start")
Nancy_end     = Int("Nancy_end")
Jason_start   = Int("Jason_start")
Jason_end     = Int("Jason_end")

# Add constraints for meeting durations (minimum required times).
s.add(Joseph_end - Joseph_start >= 60)     # Joseph requires 60 minutes.
s.add(Jeffrey_end - Jeffrey_start >= 45)     # Jeffrey requires 45 minutes.
s.add(Nancy_end - Nancy_start >= 90)         # Nancy requires 90 minutes.
s.add(Jason_end - Jason_start >= 15)         # Jason requires 15 minutes.

# Add constraints so that the meeting times lie inside each friend’s availability window.
s.add(Joseph_start >= joseph_avail_start, Joseph_end <= joseph_avail_end)
s.add(Jeffrey_start >= jeffrey_avail_start, Jeffrey_end <= jeffrey_avail_end)
s.add(Nancy_start >= nancy_avail_start, Nancy_end <= nancy_avail_end)
s.add(Jason_start >= jason_avail_start, Jason_end <= jason_avail_end)

# We assume an ordering of meetings that respects time and travel:
# Order chosen: Joseph (Russian Hill) --> Jeffrey (Financial District) --> Nancy (Alamo Square) --> Jason (North Beach)
#
# Constraint 1: Start from Bayview at 09:00 and travel to Russian Hill for Joseph.
s.add(Joseph_start >= arrival_time + travel_times[("Bayview", "Russian Hill")])
# This ensures Joseph's meeting cannot start before 09:00 + 23 = 563 minutes (i.e. 09:23).

# Constraint 2: After meeting Joseph, travel from Russian Hill to Financial District for Jeffrey.
s.add(Jeffrey_start >= Joseph_end + travel_times[("Russian Hill", "Financial District")])

# Constraint 3: After meeting Jeffrey, travel from Financial District to Alamo Square for Nancy.
s.add(Nancy_start >= Jeffrey_end + travel_times[("Financial District", "Alamo Square")])

# Constraint 4: After meeting Nancy, travel from Alamo Square to North Beach for Jason.
s.add(Jason_start >= Nancy_end + travel_times[("Alamo Square", "North Beach")])

# Check if the constraints are satisfiable.
if s.check() == sat:
    m = s.model()
    
    # Helper function: convert minutes since midnight to HH:MM (24-hour format).
    def minutes_to_HHMM(mins):
        hours = mins // 60
        minutes = mins % 60
        return f"{hours:02d}:{minutes:02d}"
    
    itinerary = []
    itinerary.append({
        "action": "meet",
        "person": "Joseph",
        "start_time": minutes_to_HHMM(m[Joseph_start].as_long()),
        "end_time": minutes_to_HHMM(m[Joseph_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Jeffrey",
        "start_time": minutes_to_HHMM(m[Jeffrey_start].as_long()),
        "end_time": minutes_to_HHMM(m[Jeffrey_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Nancy",
        "start_time": minutes_to_HHMM(m[Nancy_start].as_long()),
        "end_time": minutes_to_HHMM(m[Nancy_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Jason",
        "start_time": minutes_to_HHMM(m[Jason_start].as_long()),
        "end_time": minutes_to_HHMM(m[Jason_end].as_long())
    })
    
    import json
    # Print the itinerary in JSON format.
    print(json.dumps({"itinerary": itinerary}, indent=2))
else:
    print("No valid schedule found.")