from z3 import *

# Create an Optimizer instance
opt = Optimize()

# We'll work with absolute time in minutes from midnight.
# Pacific Heights arrival is at 9:00 (9*60 = 540).
# Define availability windows and travel lower-bound constraints (using the travel times given):
# Helen is in North Beach, available 9:00 (540) to 17:00 (1020). 
#    Minimum meeting time: 15 minutes.
#    PH -> North Beach travel: 9 minutes, so earliest start is 540+9 = 549.
# Kevin is in Mission District, available 10:45 (645) to 14:45 (885).
#    Minimum meeting time: 45 minutes.
#    PH -> Mission District travel is 15 minutes, but availability forces start >=645.
# Betty is in Financial District, available 19:00 (1140) to 21:45 (1305).
#    Minimum meeting time: 90 minutes.
#    PH -> Financial District travel: 13 minutes → earliest start 540+13 = 553 (1140 from availability is later).
# Amanda is in Alamo Square, available 19:45 (1185) to 21:00 (1260).
#    Minimum meeting time: 60 minutes.
#    PH -> Alamo Square travel: 10 minutes → earliest start 550, but availability gives 1185.

# For each friend, we introduce two Int variables: one for the start of the meeting and one for the end.
H_start, H_end = Ints('H_start H_end')
K_start, K_end = Ints('K_start K_end')
B_start, B_end = Ints('B_start B_end')
A_start, A_end = Ints('A_start A_end')

# Also, a Boolean flag to indicate whether we schedule a meeting with that friend.
H_chosen = Bool('H_chosen')
K_chosen = Bool('K_chosen')
B_chosen = Bool('B_chosen')
A_chosen = Bool('A_chosen')

# ---------------------
# Individual meeting constraints
# ---------------------
# Helen (North Beach): available 540 to 1020, earliest start 549, >=15 minutes.
opt.add(Implies(H_chosen, And(H_start >= 549, H_end <= 1020, H_end - H_start >= 15)))
# Kevin (Mission District): available 645 to 885, >=45 minutes.
opt.add(Implies(K_chosen, And(K_start >= 645, K_end <= 885, K_end - K_start >= 45)))
# Betty (Financial District): available 1140 to 1305, >=90 minutes.
opt.add(Implies(B_chosen, And(B_start >= 1140, B_end <= 1305, B_end - B_start >= 90)))
# Amanda (Alamo Square): available 1185 to 1260, >=60 minutes.
opt.add(Implies(A_chosen, And(A_start >= 1185, A_end <= 1260, A_end - A_start >= 60)))

# ---------------------
# Disjunctive ordering constraints for meetings that are actually scheduled.
# For any two friends that are both scheduled, the meetings (including travel time) must not overlap.
# We use the provided travel times between locations:
#
#   Locations and travel-times (in minutes):
#     PH -> NB : 9           ; NB -> PH : 8
#     PH -> FD : 13          ; FD -> PH : 13
#     PH -> AS : 10          ; AS -> PH : 10
#     PH -> MD : 15          ; MD -> PH : 16
#
# Between meeting locations:
#   Helen (NB) to Kevin (MD): NB->MD = 18, MD->NB = 17.
opt.add(Implies(And(H_chosen, K_chosen), 
                Or(H_end + 18 <= K_start, K_end + 17 <= H_start)))
#   Helen (NB) and Betty (FD): NB->FD = 8, FD->NB = 7.
opt.add(Implies(And(H_chosen, B_chosen), 
                Or(H_end + 8 <= B_start, B_end + 7 <= H_start)))
#   Helen (NB) and Amanda (AS): NB->AS = 16, AS->NB = 15.
opt.add(Implies(And(H_chosen, A_chosen), 
                Or(H_end + 16 <= A_start, A_end + 15 <= H_start)))
#   Kevin (MD) and Betty (FD): MD->FD = 17, FD->MD = 17.
opt.add(Implies(And(K_chosen, B_chosen), 
                Or(K_end + 17 <= B_start, B_end + 17 <= K_start)))
#   Kevin (MD) and Amanda (AS): MD->AS = 11, AS->MD = 10.
opt.add(Implies(And(K_chosen, A_chosen), 
                Or(K_end + 11 <= A_start, A_end + 10 <= K_start)))
#   Betty (FD) and Amanda (AS): FD->AS = 17, AS->FD = 17.
opt.add(Implies(And(B_chosen, A_chosen), 
                Or(B_end + 17 <= A_start, A_end + 17 <= B_start)))

# ---------------------
# Objective: we want to meet as many friends as possible.
total_meetings = If(H_chosen, 1, 0) + If(K_chosen, 1, 0) + If(B_chosen, 1, 0) + If(A_chosen, 1, 0)
opt.maximize(total_meetings)

# Secondary objective: if there is a tie in the number of meetings, prefer an earlier overall schedule.
sum_start = If(H_chosen, H_start, 0) + If(K_chosen, K_start, 0) + If(B_chosen, B_start, 0) + If(A_chosen, A_start, 0)
opt.minimize(sum_start)

# ---------------------
# Solve the scheduling problem
# ---------------------
if opt.check() == sat:
    model = opt.model()
    
    # Helper function to convert minutes-from-midnight to HH:MM string.
    def format_time(time_var):
        t = model[time_var].as_long()
        hours = t // 60
        minutes = t % 60
        return f"{hours:02d}:{minutes:02d}"
    
    itinerary = []
    # Append each meeting if it is chosen.
    if is_true(model[H_chosen]):
        itinerary.append({
            "action": "meet",
            "person": "Helen",
            "start_time": format_time(H_start),
            "end_time": format_time(H_end)
        })
    if is_true(model[K_chosen]):
        itinerary.append({
            "action": "meet",
            "person": "Kevin",
            "start_time": format_time(K_start),
            "end_time": format_time(K_end)
        })
    if is_true(model[B_chosen]):
        itinerary.append({
            "action": "meet",
            "person": "Betty",
            "start_time": format_time(B_start),
            "end_time": format_time(B_end)
        })
    if is_true(model[A_chosen]):
        itinerary.append({
            "action": "meet",
            "person": "Amanda",
            "start_time": format_time(A_start),
            "end_time": format_time(A_end)
        })
    
    # Sort the itinerary in order of meeting start times.
    def to_minutes(time_string):
        h, m = map(int, time_string.split(':'))
        return h * 60 + m
    
    itinerary.sort(key=lambda x: to_minutes(x["start_time"]))
    
    import json
    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))
else:
    print("No solution found")