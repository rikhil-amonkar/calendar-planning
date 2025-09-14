from z3 import *
import json

def format_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Input parameters in minutes since midnight
    arrival_fw = 9 * 60             # 9:00 AM => 540 minutes
    kenneth_start = 14 * 60 + 15      # 14:15 => 855 minutes
    kenneth_end = 19 * 60 + 45        # 19:45 => 1185 minutes
    travel_fw_to_nh = 11            # 11 minutes travel time

    opt = Optimize()

    # Decision variable: departure time from Fisherman's Wharf
    depart = Int('depart')
    # Decision variable: meeting end time with Kenneth (at Nob Hill)
    meet_end = Int('meet_end')
    # Meeting start time is defined by travel constraint and Kenneth's availability.
    # If we arrive (depart + travel) before Kenneth arrives then we wait until he is available.
    meet_start = If(depart + travel_fw_to_nh < kenneth_start, kenneth_start, depart + travel_fw_to_nh)

    # Add constraints:
    opt.add(depart >= arrival_fw)  # Can't depart before arriving at Fisherman's Wharf
    opt.add(meet_end <= kenneth_end)  # Must finish meeting before Kenneth departs
    opt.add(meet_end >= meet_start + 90)  # Meeting duration must be at least 90 minutes

    # Objective: maximize meeting duration with Kenneth.
    duration = meet_end - meet_start
    h1 = opt.maximize(duration)
    # Secondary objective: maximize departure time so that we leave as late as possible
    # (thus minimizing downtime waiting at Nob Hill).
    h2 = opt.maximize(depart)

    opt.check()
    model = opt.model()

    depart_val = model[depart].as_long()
    meet_end_val = model[meet_end].as_long()
    # Calculate meeting start based on the model and the if-expression.
    if depart_val + travel_fw_to_nh < kenneth_start:
        meet_start_val = kenneth_start
    else:
        meet_start_val = depart_val + travel_fw_to_nh

    itinerary = [{
        "action": "meet",
        "location": "Nob Hill",
        "person": "Kenneth",
        "start_time": format_time(meet_start_val),
        "end_time": format_time(meet_end_val)
    }]

    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))

if __name__ == '__main__':
    main()