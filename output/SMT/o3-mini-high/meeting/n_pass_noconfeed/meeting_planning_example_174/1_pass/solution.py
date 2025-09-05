import json
from z3 import *

def format_time(total_minutes):
    # Convert minutes since midnight to "H:MM" format (24-hour, no leading zero for hour)
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()

    # Travel times in minutes between locations.
    nh_to_mission = 13
    nh_to_pacific = 8
    mission_to_pacific = 16

    # Define time constants (all times in minutes after midnight)
    # Arrival at Nob Hill at 9:00AM = 540 minutes.
    start_time = 540

    # Kenneth is available at Mission District between 12:00 (720) and 15:45 (945)
    kenneth_avail_start = 720
    kenneth_avail_end = 945
    kenneth_min_duration = 45

    # Thomas is available at Pacific Heights between 15:30 (930) and 19:15 (1155)
    thomas_avail_start = 930
    thomas_avail_end = 1155
    thomas_min_duration = 75

    # Decision variables for meeting start and end times (in minutes since midnight)
    k_start = Int("k_start")
    k_end   = Int("k_end")
    t_start = Int("t_start")
    t_end   = Int("t_end")

    # Boolean decision variables: whether to meet Kenneth and Thomas.
    meet_kenneth = Bool("meet_kenneth")
    meet_thomas  = Bool("meet_thomas")

    # If not meeting, force times to default value of 0.
    opt.add(Implies(Not(meet_kenneth), And(k_start == 0, k_end == 0)))
    opt.add(Implies(Not(meet_thomas), And(t_start == 0, t_end == 0)))

    # Constraints for meeting Kenneth at Mission District.
    # You arrive at Mission District from Nob Hill after (start_time + nh_to_mission)
    opt.add(Implies(meet_kenneth, And(
        # Must not start before Kenneth is available and after travel from Nob Hill.
        k_start >= kenneth_avail_start, 
        k_start >= start_time + nh_to_mission,
        # Meeting must finish by Kenneth's availability end.
        k_end <= kenneth_avail_end,
        # Meeting duration is at least the minimum required.
        k_end - k_start >= kenneth_min_duration
    )))

    # Constraints for meeting Thomas at Pacific Heights.
    # There are two cases: if Kenneth is met, you travel from Mission District;
    # otherwise, you travel directly from Nob Hill.
    opt.add(Implies(meet_thomas, And(
        t_start >= thomas_avail_start, 
        t_start >= If(meet_kenneth, k_end + mission_to_pacific, start_time + nh_to_pacific),
        t_end <= thomas_avail_end,
        t_end - t_start >= thomas_min_duration
    )))

    # Objective: maximize the number of friends met.
    total_meetings = If(meet_kenneth, 1, 0) + If(meet_thomas, 1, 0)
    opt.maximize(total_meetings)

    # Solve the optimization problem
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        if is_true(model.evaluate(meet_kenneth)):
            itinerary.append({
                "action": "meet",
                "location": "Mission District",
                "person": "Kenneth",
                "start_time": format_time(model[k_start].as_long()),
                "end_time": format_time(model[k_end].as_long())
            })
        if is_true(model.evaluate(meet_thomas)):
            itinerary.append({
                "action": "meet",
                "location": "Pacific Heights",
                "person": "Thomas",
                "start_time": format_time(model[t_start].as_long()),
                "end_time": format_time(model[t_end].as_long())
            })
        schedule = {"itinerary": itinerary}
        print(json.dumps(schedule, indent=2))
    else:
        # If no schedule is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()