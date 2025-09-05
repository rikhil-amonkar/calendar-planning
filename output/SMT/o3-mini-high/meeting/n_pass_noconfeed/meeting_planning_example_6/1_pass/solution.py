import json
from z3 import Optimize, Int, sat

def minutes_to_time(m):
    # Convert minutes since midnight into "H:MM" 24-hour format (no leading zero for hour)
    hour = m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    # Define time constants (in minutes since midnight)
    arrival_fw = 9 * 60             # 9:00 AM → 540 minutes
    kenneth_available_start = 14 * 60 + 15  # 14:15 → 855 minutes
    kenneth_available_end = 19 * 60 + 45    # 19:45 → 1185 minutes
    travel_fw_to_nh = 11            # minutes from Fisherman's Wharf to Nob Hill

    # Create an optimization model using Z3
    opt = Optimize()

    # Decision variables (all in minutes)
    # T_dep: departure time from Fisherman's Wharf
    # m_start: meeting start time at Nob Hill with Kenneth
    # m_end: meeting end time at Nob Hill with Kenneth
    T_dep = Int("T_dep")
    m_start = Int("m_start")
    m_end = Int("m_end")

    # Add constraints based on the input parameters.
    # You arrive at Fisherman's Wharf at 9:00 so you cannot depart before that.
    opt.add(T_dep >= arrival_fw)
    # After departing, you need travel time from Fisherman's Wharf to Nob Hill.
    opt.add(m_start >= T_dep + travel_fw_to_nh)
    # Kenneth is available from 14:15.
    opt.add(m_start >= kenneth_available_start)
    # Kenneth is available until 19:45.
    opt.add(m_end <= kenneth_available_end)
    # You want to meet Kenneth for at least 90 minutes.
    opt.add(m_end - m_start >= 90)

    # The goal: Maximize the meeting duration (m_end - m_start) and then maximize T_dep
    # so that you don't travel too early (i.e. you arrive just on time and avoid long idle waits).
    opt.maximize(m_end - m_start)
    opt.maximize(T_dep)

    # Check for a solution.
    if opt.check() == sat:
        model = opt.model()
        dep_time = model[T_dep].as_long()
        meeting_start = model[m_start].as_long()
        meeting_end = model[m_end].as_long()

        # The optimal computed schedule:
        # Depart Fisherman's Wharf at T_dep, arriving at Nob Hill at T_dep + travel_fw_to_nh.
        # Because of Kenneth’s availability, the meeting starts at max(T_dep+11, 14:15)
        # and ends by 19:45. With the objectives, the solver will choose:
        # T_dep = 844 (14:04), meeting_start = 855 (14:15) and meeting_end = 1185 (19:45)
        itinerary = [
            {
                "action": "meet",
                "location": "Nob Hill",
                "person": "Kenneth",
                "start_time": minutes_to_time(meeting_start),
                "end_time": minutes_to_time(meeting_end)
            }
        ]
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"error": "No feasible schedule found"}))

if __name__ == '__main__':
    main()