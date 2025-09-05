import json
from z3 import Optimize, Int, sat

def minutes_to_time(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Time parameters (in minutes from midnight)
    arrival_sunset = 9 * 60             # 9:00 AM => 540 minutes
    joshua_start = 20 * 60 + 45          # 20:45 => 1245 minutes
    joshua_end   = 21 * 60 + 45          # 21:45 => 1305 minutes

    # Travel time (in minutes)
    travel_sunset_to_ggp = 11           # Sunset District -> Golden Gate Park
    travel_ggp_to_sunset = 10           # Golden Gate Park -> Sunset District

    # Create an optimizer instance from Z3
    opt = Optimize()

    # Decision variables:
    # depart: time you leave the Sunset District (in minutes from midnight)
    # m_start: start time of meeting with Joshua at Golden Gate Park
    # m_end: end time of meeting with Joshua at Golden Gate Park
    depart = Int("depart")
    m_start = Int("m_start")
    m_end = Int("m_end")

    # Add constraints:
    # 1. You arrive at Sunset District at 9:00AM so departure cannot be before that.
    opt.add(depart >= arrival_sunset)
    # To be on time for Joshua's availability, you must arrive at Golden Gate Park no later than his start time.
    # Arrival time at Golden Gate Park is depart + travel time.
    # Thus: depart + travel_sunset_to_ggp <= joshua_start.
    opt.add(depart <= joshua_start - travel_sunset_to_ggp)

    # 2. You cannot start meeting before arriving at Golden Gate Park.
    opt.add(m_start >= depart + travel_sunset_to_ggp)
    # 3. Joshua is only available from 20:45 onward.
    opt.add(m_start >= joshua_start)
    # 4. The meeting must occur while Joshua is available.
    opt.add(m_end <= joshua_end)
    # 5. You'd like to meet Joshua for at least 15 minutes.
    opt.add(m_end >= m_start + 15)

    # Objective: maximize meeting duration (m_end - m_start)
    meeting_duration = m_end - m_start
    opt.maximize(meeting_duration)
    # Secondary objective: maximize departure time (to minimize waiting at Golden Gate Park)
    opt.maximize(depart)

    # Check for solution
    if opt.check() == sat:
        model = opt.model()
        m_start_val = model[m_start].as_long()
        m_end_val = model[m_end].as_long()

        itinerary = {
            "itinerary": [
                {
                    "action": "meet",
                    "location": "Golden Gate Park",
                    "person": "Joshua",
                    "start_time": minutes_to_time(m_start_val),
                    "end_time": minutes_to_time(m_end_val)
                }
            ]
        }
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"error": "No solution found"}, indent=2))

if __name__ == '__main__':
    main()