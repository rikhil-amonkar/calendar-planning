import json
from z3 import Optimize, Int, Bool, If, And, Not, Implies, sat

def minutes_to_time_str(m):
    # Convert an integer number of minutes (since midnight) into "H:MM" 24-hour format.
    h = m // 60
    m_rem = m % 60
    return f"{h}:{m_rem:02d}"

def main():
    # Create the Optimize solver instance
    opt = Optimize()

    # Starting parameters
    start_time = 540  # 9:00 AM in minutes

    # Travel times (in minutes)
    travel_Sunset_NorthBeach = 29
    travel_Sunset_Chinatown = 30
    travel_Sunset_RussianHill = 24
    travel_NorthBeach_Chinatown = 6
    travel_NorthBeach_RussianHill = 4
    travel_Chinatown_RussianHill = 7

    # Meeting windows and minimum durations (in minutes)
    # Melissa: available 8:15 (495) to 13:30 (810), min meeting 105 minutes, at North Beach.
    # Anthony: available 13:15 (795) to 14:30 (870), min meeting 60 minutes, at Chinatown.
    # Rebecca: available 19:30 (1170) to 21:15 (1275), min meeting 105 minutes, at Russian Hill.

    # Define integer time variables for the start and end times of each meeting
    s_mel = Int('s_melissa_start')
    e_mel = Int('e_melissa_end')
    s_ant = Int('s_anthony_start')
    e_ant = Int('e_anthony_end')
    s_reb = Int('s_rebecca_start')
    e_reb = Int('e_rebecca_end')

    # Define Boolean variables indicating whether a meeting is scheduled
    m_mel = Bool('meet_melissa')
    m_ant = Bool('meet_anthony')
    m_reb = Bool('meet_rebecca')

    # Constraints for Melissa's meeting at North Beach:
    # Must depart from Sunset District at 9:00 and travel to North Beach.
    opt.add(Implies(m_mel, s_mel >= start_time + travel_Sunset_NorthBeach))
    # Must meet within Melissa's availability window and for at least 105 minutes.
    opt.add(Implies(m_mel, s_mel >= 495))  # available from 8:15, but arrival is later anyway.
    opt.add(Implies(m_mel, e_mel <= 810))   # available until 13:30
    opt.add(Implies(m_mel, e_mel - s_mel >= 105))

    # Constraints for Anthony's meeting at Chinatown:
    # Must meet within Anthony's availability window and for at least 60 minutes.
    opt.add(Implies(m_ant, s_ant >= 795))   # available from 13:15
    opt.add(Implies(m_ant, e_ant <= 870))     # available until 14:30
    opt.add(Implies(m_ant, e_ant - s_ant >= 60))
    # If Melissa was met before Anthony, then add travel time from North Beach to Chinatown.
    opt.add(Implies(And(m_ant, m_mel), s_ant >= e_mel + travel_NorthBeach_Chinatown))
    # If Melissa was not met, travel from Sunset District to Chinatown.
    opt.add(Implies(And(m_ant, Not(m_mel)), s_ant >= start_time + travel_Sunset_Chinatown))

    # Constraints for Rebecca's meeting at Russian Hill:
    # Must meet within Rebecca's availability window and for at least 105 minutes.
    opt.add(Implies(m_reb, s_reb >= 1170))  # available from 19:30
    opt.add(Implies(m_reb, e_reb <= 1275))   # available until 21:15
    opt.add(Implies(m_reb, e_reb - s_reb >= 105))
    # Ordering for Rebecca: if Anthony was met, travel from Chinatown to Russian Hill.
    opt.add(Implies(And(m_reb, m_ant), s_reb >= e_ant + travel_Chinatown_RussianHill))
    # Else if Anthony wasn't met but Melissa was met, travel from North Beach to Russian Hill.
    opt.add(Implies(And(m_reb, Not(m_ant), m_mel), s_reb >= e_mel + travel_NorthBeach_RussianHill))
    # Else, if neither Anthony nor Melissa were met, travel from Sunset District to Russian Hill.
    opt.add(Implies(And(m_reb, Not(m_ant), Not(m_mel)), s_reb >= start_time + travel_Sunset_RussianHill))

    # Ensure time variables are non-negative (for safety)
    opt.add(s_mel >= 0, e_mel >= 0, s_ant >= 0, e_ant >= 0, s_reb >= 0, e_reb >= 0)

    # Set objective: maximize the number of meetings scheduled
    total_meetings = If(m_mel, 1, 0) + If(m_ant, 1, 0) + If(m_reb, 1, 0)
    opt.maximize(total_meetings)

    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
        itinerary = []
        # For each scheduled meeting, add an event with the computed times.
        if model.evaluate(m_mel):
            start_val = model.evaluate(s_mel).as_long()
            end_val = model.evaluate(e_mel).as_long()
            itinerary.append({
                "action": "meet",
                "location": "North Beach",
                "person": "Melissa",
                "start_time": minutes_to_time_str(start_val),
                "end_time": minutes_to_time_str(end_val)
            })
        if model.evaluate(m_ant):
            start_val = model.evaluate(s_ant).as_long()
            end_val = model.evaluate(e_ant).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Chinatown",
                "person": "Anthony",
                "start_time": minutes_to_time_str(start_val),
                "end_time": minutes_to_time_str(end_val)
            })
        if model.evaluate(m_reb):
            start_val = model.evaluate(s_reb).as_long()
            end_val = model.evaluate(e_reb).as_long()
            itinerary.append({
                "action": "meet",
                "location": "Russian Hill",
                "person": "Rebecca",
                "start_time": minutes_to_time_str(start_val),
                "end_time": minutes_to_time_str(end_val)
            })

        # Sort the events by their start time
        def get_start(event):
            parts = event["start_time"].split(":")
            return int(parts[0]) * 60 + int(parts[1])
        itinerary.sort(key=get_start)

        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()