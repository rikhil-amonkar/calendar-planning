#!/usr/bin/env python
from z3 import *
import json

# Helper function: convert minutes-since-midnight to "H:MM" string (24-hour format, no leading zero for hour)
def minutes_to_str(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

# ----- Data for Friends and Travel Times -----
# Friend data: each friend is represented by an index (0..8)
# friend_names, locations, availability window (in minutes from midnight), and minimum meeting duration (in minutes)
friend_names = [
    "Jeffrey",    # 0
    "Ronald",     # 1
    "Jason",      # 2
    "Melissa",    # 3
    "Elizabeth",  # 4
    "Margaret",   # 5
    "George",     # 6
    "Richard",    # 7
    "Laura"       # 8
]

locations = [
    "Fisherman's Wharf",  # Jeffrey
    "Alamo Square",       # Ronald
    "Financial District", # Jason
    "Union Square",       # Melissa
    "Sunset District",    # Elizabeth
    "Embarcadero",        # Margaret
    "Golden Gate Park",   # George
    "Chinatown",          # Richard
    "Richmond District"   # Laura
]

# Availability times in minutes (from midnight)
avail_start = [
    10 * 60 + 15,  # Jeffrey: 10:15
    7 * 60 + 45,   # Ronald: 7:45 (but we start only at 9:00, so effective start is later)
    10 * 60 + 45,  # Jason: 10:45
    17 * 60 + 45,  # Melissa: 17:45
    14 * 60 + 45,  # Elizabeth: 14:45
    13 * 60 + 15,  # Margaret: 13:15
    19 * 60,       # George: 19:00
    9 * 60 + 30,   # Richard: 9:30
    9 * 60 + 45    # Laura: 9:45
]

avail_end = [
    13 * 60,     # Jeffrey: 13:00
    14 * 60 + 45, # Ronald: 14:45
    16 * 60,     # Jason: 16:00
    18 * 60 + 15,# Melissa: 18:15
    17 * 60 + 30,# Elizabeth: 17:30
    19 * 60,     # Margaret: 19:00
    22 * 60,     # George: 22:00
    21 * 60,     # Richard: 21:00
    18 * 60      # Laura: 18:00
]

meeting_duration = [
    90,  # Jeffrey: 90 minutes
    120, # Ronald: 120 minutes
    105, # Jason: 105 minutes
    15,  # Melissa: 15 minutes
    105, # Elizabeth: 105 minutes
    90,  # Margaret: 90 minutes
    75,  # George: 75 minutes
    15,  # Richard: 15 minutes
    60   # Laura: 60 minutes
]

# Travel times (in minutes) from Presidio (our start location) to each friend's location.
# We start at Presidio at 9:00 (9:00 = 540 minutes)
start_travel = [
    19, # Presidio to Fisherman's Wharf (Jeffrey)
    19, # Presidio to Alamo Square (Ronald)
    23, # Presidio to Financial District (Jason)
    22, # Presidio to Union Square (Melissa)
    15, # Presidio to Sunset District (Elizabeth)
    20, # Presidio to Embarcadero (Margaret)
    12, # Presidio to Golden Gate Park (George)
    21, # Presidio to Chinatown (Richard)
    7   # Presidio to Richmond District (Laura)
]

# Travel time matrix between friends' locations.
# The matrix is indexed by friend indices corresponding to their locations.
# Rows: from, Columns: to.
travel_matrix = [
    # 0: Fisherman's Wharf
    [0,   21, 11, 13, 27,  8, 25, 12, 18],
    # 1: Alamo Square
    [19,   0, 17, 14, 16, 16,  9, 15, 11],
    # 2: Financial District
    [10,  17,  0,  9, 30,  4, 23,  5, 21],
    # 3: Union Square
    [15,  15,  9,  0, 27, 11, 22,  7, 20],
    # 4: Sunset District
    [29,  17, 30, 30,  0, 30, 11, 30, 12],
    # 5: Embarcadero
    [6,   19,  5, 10, 30,  0, 25,  7, 21],
    # 6: Golden Gate Park
    [24,   9, 26, 22, 10, 25,  0, 23,  7],
    # 7: Chinatown
    [8,   17,  5,  7, 29,  5, 23,  0, 20],
    # 8: Richmond District
    [18,  13, 22, 21, 11, 19,  9, 20,  0]
]

# Number of meeting slots: at most one meeting per friend => 9 slots maximum.
n_slots = 9

# ----- Z3 Model Setup -----
opt = Optimize()

# Create decision variables for each slot.
# friend_vars[i] will be an integer: -1 means the slot is unused; 0..8 indicate which friend is scheduled.
friend_vars = [Int(f"friend_{i}") for i in range(n_slots)]
# start_vars[i] is the start time (in minutes from midnight) of the meeting in slot i (if used)
start_vars = [Int(f"start_{i}") for i in range(n_slots)]

# Domain constraints: friend_vars[i] ∈ {-1} ∪ {0,...,8} and start_vars between 0 and 1440.
for i in range(n_slots):
    opt.add(Or(friend_vars[i] == -1, And(friend_vars[i] >= 0, friend_vars[i] <= 8)))
    opt.add(start_vars[i] >= 0, start_vars[i] <= 1440)

# If a slot is unused (friend = -1), then all later slots must also be unused.
for i in range(n_slots - 1):
    opt.add(Implies(friend_vars[i] == -1, friend_vars[i+1] == -1))

# Helper: Given a Z3 integer variable f representing a friend index, return an expression for the start travel time 
# from Presidio to that friend's location.
def pre_travel_expr(f):
    return Sum([If(f == i, start_travel[i], 0) for i in range(len(start_travel))])

# Helper: Given two Z3 integer variables a and b representing friend indices, return an expression for travel time 
# between their locations, according to travel_matrix.
def travel_expr(a, b):
    expr = Sum([If(And(a == i, b == j), travel_matrix[i][j], 0)
                for i in range(len(travel_matrix))
                for j in range(len(travel_matrix[0]))])
    return expr

# Availability and meeting duration constraints for each used slot.
for i in range(n_slots):
    # For each possible friend k, if this slot is assigned friend k then:
    for k in range(len(friend_names)):
        # Meeting must start no earlier than the friend's availability start
        opt.add(Implies(friend_vars[i] == k, start_vars[i] >= avail_start[k]))
        # And meeting must finish by the friend's availability end.
        opt.add(Implies(friend_vars[i] == k, start_vars[i] + meeting_duration[k] <= avail_end[k]))
    # If slot is not used, no meeting constraints are needed.

# Initial travel constraint for slot 0: meeting start must be at least 9:00 (540) plus travel time from Presidio.
for k in range(len(friend_names)):
    opt.add(Implies(friend_vars[0] == k, start_vars[0] >= 540 + start_travel[k]))

# For consecutive meeting slots: if both slot i and slot i+1 are used, then ensure enough time for meeting and travel.
for i in range(n_slots - 1):
    # If both slots are used then:
    duration_expr = Sum([If(friend_vars[i] == k, meeting_duration[k], 0) for k in range(len(friend_names))])
    opt.add(Implies(And(friend_vars[i] != -1, friend_vars[i+1] != -1),
                    start_vars[i+1] >= start_vars[i] + duration_expr + travel_expr(friend_vars[i], friend_vars[i+1])))

# Ensure that each friend is met at most once: distinct friend assignments among used slots.
for i in range(n_slots):
    for j in range(i+1, n_slots):
        opt.add(Implies(And(friend_vars[i] != -1, friend_vars[j] != -1),
                        friend_vars[i] != friend_vars[j]))

# Objective: maximize the total number of meetings scheduled.
meeting_count = Sum([If(friend_vars[i] != -1, 1, 0) for i in range(n_slots)])
h = opt.maximize(meeting_count)

# Solve the optimization problem.
if opt.check() == sat:
    model = opt.model()
    itinerary = []
    for i in range(n_slots):
        # If slot is used, friend_vars[i] != -1.
        friend_val = model.evaluate(friend_vars[i]).as_long()
        if friend_val == -1:
            break  # All subsequent slots are unused.
        start_time = model.evaluate(start_vars[i]).as_long()
        dur = meeting_duration[friend_val]
        end_time = start_time + dur
        meeting = {
            "action": "meet",
            "location": locations[friend_val],
            "person": friend_names[friend_val],
            "start_time": minutes_to_str(start_time),
            "end_time": minutes_to_str(end_time)
        }
        itinerary.append(meeting)
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print(json.dumps({"itinerary": []}))