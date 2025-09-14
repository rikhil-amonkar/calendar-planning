from z3 import Optimize, Int, sat
import json

def minutes_to_time(t):
    hours = t // 60
    minutes = t % 60
    return f"{hours}:{minutes:02d}"

def main():
    opt = Optimize()

    # Define variables for meeting start and end times in minutes from midnight.
    m_start = Int('m_start')
    m_end   = Int('m_end')
    a_start = Int('a_start')
    a_end   = Int('a_end')
    r_start = Int('r_start')
    r_end   = Int('r_end')

    # Given fixed times (in minutes from midnight)
    # Arrival: Sunset District at 9:00 -> 9*60 = 540.
    # Melissa available (North Beach): 8:15 (495) to 13:30 (810); min meeting = 105 minutes.
    # Anthony available (Chinatown): 13:15 (795) to 14:30 (870); min meeting = 60 minutes.
    # Rebecca available (Russian Hill): 19:30 (1170) to 21:15 (1275); min meeting = 105 minutes.
    #
    # Travel times (in minutes):
    # Sunset District -> North Beach: 29
    # North Beach -> Chinatown: 6
    # Chinatown -> Russian Hill: 7

    # Constraints for Melissa at North Beach:
    # Must arrive from Sunset District: 540 + 29 = 569 minutes or later.
    opt.add(m_start >= 540 + 29)  # m_start >= 569
    # Ensure the meeting fits in Melissa's availability window:
    opt.add(m_start <= 810 - 105)  # m_start <= 705 so that m_start + 105 <= 810
    # Fix meeting duration to the minimum required (could be longer; here we set it optimally to minimum)
    opt.add(m_end == m_start + 105)
    opt.add(m_end <= 810)

    # Constraints for Anthony at Chinatown:
    opt.add(a_start >= 795)  # Must not start before 13:15
    # Must arrive after finishing Melissa meeting plus travel time from North Beach to Chinatown (6 minutes)
    opt.add(a_start >= m_end + 6)
    opt.add(a_start <= 870 - 60)  # Ensures a_start + 60 <= 870, so a_start <= 810
    opt.add(a_end == a_start + 60)
    opt.add(a_end <= 870)

    # Constraints for Rebecca at Russian Hill:
    opt.add(r_start >= 1170)  # Must not start before 19:30
    # Must arrive after finishing Anthony meeting plus travel time from Chinatown to Russian Hill (7 minutes)
    opt.add(r_start >= a_end + 7)
    # To fit exactly into Rebecca's window, we force the meeting to start at the only possible time:
    opt.add(r_start <= 1275 - 105)  # r_start <= 1170 so r_start == 1170
    opt.add(r_end == r_start + 105)
    opt.add(r_end <= 1275)

    # Use optimization objectives to choose the earliest feasible times for each meeting.
    h1 = opt.minimize(m_start)
    h2 = opt.minimize(a_start)
    h3 = opt.minimize(r_start)

    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        itinerary.append({
            "action": "meet",
            "location": "North Beach",
            "person": "Melissa",
            "start_time": minutes_to_time(model[m_start].as_long()),
            "end_time": minutes_to_time(model[m_end].as_long())
        })
        itinerary.append({
            "action": "meet",
            "location": "Chinatown",
            "person": "Anthony",
            "start_time": minutes_to_time(model[a_start].as_long()),
            "end_time": minutes_to_time(model[a_end].as_long())
        })
        itinerary.append({
            "action": "meet",
            "location": "Russian Hill",
            "person": "Rebecca",
            "start_time": minutes_to_time(model[r_start].as_long()),
            "end_time": minutes_to_time(model[r_end].as_long())
        })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()