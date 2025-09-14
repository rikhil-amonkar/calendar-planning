from z3 import *
import json

def minutes_to_time(minutes):
    hours = minutes // 60
    mins = minutes % 60
    return f"{hours}:{mins:02d}"

def main():
    # Create an Optimize object
    opt = Optimize()
    
    # Decision variables for meeting start times (in minutes after midnight)
    s_S = Int("s_S")  # Sarah's meeting start time
    s_J = Int("s_J")  # Jeffrey's meeting start time
    s_B = Int("s_B")  # Brian's meeting start time

    # Decision variables for meeting end times
    e_S = Int("e_S")
    e_J = Int("e_J")
    e_B = Int("e_B")

    # Boolean variables for whether we attend the meeting with each friend
    attend_S = Bool("attend_S")
    attend_J = Bool("attend_J")
    attend_B = Bool("attend_B")
    
    # Availability windows and minimum durations:
    # Times are in minutes from midnight.
    # You arrive at Sunset District at 9:00 (540) but each friend’s window is later.
    # Sarah is at North Beach from 16:00 (960) to 18:15 (1095) with min 60 minutes.
    # Jeffrey is at Union Square from 15:00 (900) to 22:00 (1320) with min 75 minutes.
    # Brian is at Alamo Square from 16:00 (960) to 17:30 (1050) with min 75 minutes.
    
    # If a meeting is scheduled, its start must lie in the allowed window.
    # If not scheduled, force the start time to 0.
    opt.add(If(attend_S, And(s_S >= 960, s_S <= 1035), s_S == 0))
    opt.add(If(attend_J, And(s_J >= 900, s_J <= 1245), s_J == 0))
    opt.add(If(attend_B, And(s_B >= 960, s_B <= 975), s_B == 0))
    
    # Define meeting end times: if attended, the meeting lasts exactly the minimum duration.
    # (We meet the minimum requirement; extra slack isn’t needed for the purpose of scheduling.)
    opt.add(If(attend_S, e_S == s_S + 60, e_S == 0))
    opt.add(If(attend_J, e_J == s_J + 75, e_J == 0))
    opt.add(If(attend_B, e_B == s_B + 75, e_B == 0))
    
    # Travel times in minutes between locations:
    # Locations: Sunset District, North Beach (Sarah), Union Square (Jeffrey), Alamo Square (Brian)
    # Given travel times:
    #   Sunset -> North Beach: 29, Sunset -> Union Square: 30, Sunset -> Alamo Square: 17
    #   North Beach -> Union Square: 7, North Beach -> Alamo Square: 16
    #   Union Square -> North Beach: 10, Union Square -> Alamo Square: 15
    #   Alamo Square -> North Beach: 15, Alamo Square -> Union Square: 14
    #
    # When scheduling back-to-back meetings, we must add the travel time from one location to the next.
    #
    # For any two meetings that are both scheduled, one must come before the other.
    # We model this by a disjunction for each pair.
    
    # Sarah (North Beach) and Jeffrey (Union Square):
    # Either Sarah comes before Jeffrey: Sarah meeting ends then plus travel time (7 minutes) <= Jeffrey start,
    # or Jeffrey comes before Sarah: Jeffrey meeting ends then plus travel time (10 minutes) <= Sarah start.
    opt.add(Implies(And(attend_S, attend_J),
                     Or(s_S + 60 + 7 <= s_J, s_J + 75 + 10 <= s_S)))
    
    # Sarah (North Beach) and Brian (Alamo Square):
    # Either Sarah then Brian: s_S + 60 + 16 <= s_B,
    # or Brian then Sarah: s_B + 75 + 15 <= s_S.
    opt.add(Implies(And(attend_S, attend_B),
                     Or(s_S + 60 + 16 <= s_B, s_B + 75 + 15 <= s_S)))
    
    # Jeffrey (Union Square) and Brian (Alamo Square):
    # Either Jeffrey then Brian: s_J + 75 + 15 <= s_B,
    # or Brian then Jeffrey: s_B + 75 + 14 <= s_J.
    opt.add(Implies(And(attend_J, attend_B),
                     Or(s_J + 75 + 15 <= s_B, s_B + 75 + 14 <= s_J)))
    
    # Our primary objective is to maximize the number of friends we meet.
    num_meetings = If(attend_S, 1, 0) + If(attend_J, 1, 0) + If(attend_B, 1, 0)
    h1 = opt.maximize(num_meetings)
    
    # Secondary objective: minimize the total finishing time of attended meetings,
    # encouraging an itinerary that ends as early as possible.
    total_end = If(attend_S, e_S, 0) + If(attend_J, e_J, 0) + If(attend_B, e_B, 0)
    h2 = opt.minimize(total_end)
    
    # Check for a solution
    if opt.check() == sat:
        model = opt.model()
    else:
        print(json.dumps({"itinerary": []}))
        return

    # Build the itinerary by collecting the meetings that are scheduled.
    itinerary = []
    if is_true(model.eval(attend_S)):
        start = model.eval(s_S).as_long()
        end = model.eval(e_S).as_long()
        itinerary.append({
            "action": "meet",
            "location": "North Beach",
            "person": "Sarah",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        
    if is_true(model.eval(attend_J)):
        start = model.eval(s_J).as_long()
        end = model.eval(e_J).as_long()
        itinerary.append({
            "action": "meet",
            "location": "Union Square",
            "person": "Jeffrey",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })
        
    if is_true(model.eval(attend_B)):
        start = model.eval(s_B).as_long()
        end = model.eval(e_B).as_long()
        itinerary.append({
            "action": "meet",
            "location": "Alamo Square",
            "person": "Brian",
            "start_time": minutes_to_time(start),
            "end_time": minutes_to_time(end)
        })

    # Sort the itinerary by start time
    def sort_key(meeting):
        t = meeting["start_time"]
        parts = t.split(":")
        return int(parts[0]) * 60 + int(parts[1])
    itinerary.sort(key=sort_key)

    result = {"itinerary": itinerary}
    print(json.dumps(result, indent=2))

if __name__ == '__main__':
    main()