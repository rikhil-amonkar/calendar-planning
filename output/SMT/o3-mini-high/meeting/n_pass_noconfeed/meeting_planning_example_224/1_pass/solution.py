import json
from z3 import Int, Optimize, sat

def minutes_to_time(m):
    # Convert minutes from midnight to H:MM 24-hour format without a leading zero for hours.
    h = m // 60
    mm = m % 60
    return f"{h}:{mm:02d}"

def main():
    opt = Optimize()

    # Declare SMT integer variables for the meeting start and end times (in minutes after midnight)
    m_melissa_start = Int("m_melissa_start")  # Melissa meeting at Golden Gate Park
    m_melissa_end   = Int("m_melissa_end")
    m_emily_start   = Int("m_emily_start")    # Emily meeting at Richmond District
    m_emily_end     = Int("m_emily_end")
    m_nancy_start   = Int("m_nancy_start")    # Nancy meeting at Presidio
    m_nancy_end     = Int("m_nancy_end")
    
    # Constants: times in minutes from midnight
    arrival_FW = 9 * 60  # 9:00AM = 540
    # Travel durations between locations (in minutes)
    travel_FW_to_GGP = 25
    travel_GGP_to_RD = 7
    travel_RD_to_PRES = 7
    
    # Minimum meeting durations (in minutes)
    min_dur_melissa = 15
    min_dur_emily   = 120
    min_dur_nancy   = 105

    # Availability windows (in minutes after midnight)
    # Melissa at Golden Gate Park: 8:30AM to 8:00PM
    melissa_avail_start = 8 * 60 + 30   # 510
    melissa_avail_end   = 20 * 60         # 1200
    # Emily at Richmond District: 4:45PM to 10:00PM
    emily_avail_start   = 16 * 60 + 45    # 1005
    emily_avail_end     = 22 * 60         # 1320
    # Nancy at Presidio: 7:45PM to 10:00PM
    nancy_avail_start   = 19 * 60 + 45    # 1185
    nancy_avail_end     = 22 * 60         # 1320

    # -------------------------------
    # Add constraints for Melissa meeting (Golden Gate Park)
    # Must arrive after starting at Fisherman's Wharf plus travel time
    opt.add(m_melissa_start >= arrival_FW + travel_FW_to_GGP)  # >= 540 + 25 = 565
    # Meeting must be within Melissa's available window
    opt.add(m_melissa_start >= melissa_avail_start)
    opt.add(m_melissa_end <= melissa_avail_end)
    # Meeting duration constraint for Melissa
    opt.add(m_melissa_end - m_melissa_start >= min_dur_melissa)
    
    # -------------------------------
    # Add constraints for Emily meeting (Richmond District)
    # Travel from Golden Gate Park to Richmond District takes 7 minutes.
    opt.add(m_emily_start >= m_melissa_end + travel_GGP_to_RD)
    # Emily is available from 16:45 onward.
    opt.add(m_emily_start >= emily_avail_start)
    opt.add(m_emily_end <= emily_avail_end)
    opt.add(m_emily_end - m_emily_start >= min_dur_emily)
    
    # -------------------------------
    # Add constraints for Nancy meeting (Presidio)
    # Travel from Richmond District to Presidio takes 7 minutes.
    opt.add(m_nancy_start >= m_emily_end + travel_RD_to_PRES)
    # Nancy becomes available at 7:45PM
    opt.add(m_nancy_start >= nancy_avail_start)
    opt.add(m_nancy_end <= nancy_avail_end)
    opt.add(m_nancy_end - m_nancy_start >= min_dur_nancy)
    
    # -------------------------------
    # Objective: We want to meet as many friends as possible.
    # Since all three meetings are feasible, we optimize for the earliest finishing schedule.
    # Minimizing the end time of Nancy's meeting (which is last in the sequence) reduces wasted waiting time.
    opt.minimize(m_nancy_end)

    if opt.check() == sat:
        model = opt.model()
        # Build the itinerary list with computed times (convert minutes to H:MM strings)
        itinerary = [
            {
                "action": "meet",
                "location": "Golden Gate Park",
                "person": "Melissa",
                "start_time": minutes_to_time(model[m_melissa_start].as_long()),
                "end_time": minutes_to_time(model[m_melissa_end].as_long())
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Emily",
                "start_time": minutes_to_time(model[m_emily_start].as_long()),
                "end_time": minutes_to_time(model[m_emily_end].as_long())
            },
            {
                "action": "meet",
                "location": "Presidio",
                "person": "Nancy",
                "start_time": minutes_to_time(model[m_nancy_start].as_long()),
                "end_time": minutes_to_time(model[m_nancy_end].as_long())
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # If no solution is found, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()