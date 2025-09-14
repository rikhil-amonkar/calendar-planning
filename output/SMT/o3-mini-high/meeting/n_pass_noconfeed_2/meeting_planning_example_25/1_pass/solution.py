import json
from z3 import *

def minutes_to_time(m):
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Time constants in minutes after midnight
    start_GGP = 9 * 60           # 9:00 AM -> 540 minutes
    David_start = 16 * 60        # 16:00 -> 960 minutes
    David_end = 21 * 60 + 45     # 21:45 -> 1305 minutes
    travel_GGP_to_CT = 23        # minutes from Golden Gate Park to Chinatown

    # Z3 integer variables (all times in minutes after midnight)
    t_dep = Int('t_dep')         # Departure time from Golden Gate Park
    t_meet_end = Int('t_meet_end')  # End time of meeting with David in Chinatown

    # meeting_start is defined as the later of arrival time at Chinatown (t_dep+travel)
    # and David's available start time.
    meeting_start = If(t_dep + travel_GGP_to_CT >= David_start, t_dep + travel_GGP_to_CT, David_start)
    meeting_duration = t_meet_end - meeting_start

    # Create an optimizer instance.
    opt = Optimize()

    # Constraints:
    # 1. You arrive at Golden Gate Park at 9:00 AM so you cannot depart before that.
    opt.add(t_dep >= start_GGP)
    # 2. David is available until 21:45.
    opt.add(t_meet_end <= David_end)
    # 3. You want to meet David for at least 105 minutes.
    opt.add(meeting_duration >= 105)
    # 4. Meeting must end after it starts.
    opt.add(t_meet_end >= meeting_start)

    # Objectives:
    # Primary: Maximize the meeting duration with David.
    # (This will push t_meet_end to its maximum allowable value and meeting_start as early as possible.)
    h1 = opt.maximize(meeting_duration)
    # Secondary: Maximize the departure time from Golden Gate Park to leave as late as possible,
    # so you can meet other friends at Golden Gate Park before heading to Chinatown.
    h2 = opt.maximize(t_dep)

    if opt.check() == sat:
        m = opt.model()
        dep_val = m[t_dep].as_long()             # Optimal departure from Golden Gate Park
        # Arrival time in Chinatown = departure time + travel time:
        arr_time = dep_val + travel_GGP_to_CT
        # meeting_start is the maximum of arrival and David's start time
        meet_start_val = arr_time if arr_time >= David_start else David_start
        meet_end_val = m[t_meet_end].as_long()     # Meeting end time in Chinatown

        # Build itinerary:
        # Event 1: While at Golden Gate Park, meet a friend (e.g., Alice) until you leave.
        # Event 2: Meet David in Chinatown.
        itinerary = [
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Alice",
                "start_time": minutes_to_time(start_GGP),
                "end_time": minutes_to_time(dep_val)
            },
            {
                "action": "meet",
                "location": "Chinatown",
                "person": "David",
                "start_time": minutes_to_time(meet_start_val),
                "end_time": minutes_to_time(meet_end_val)
            }
        ]

        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()