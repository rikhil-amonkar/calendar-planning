import json
from z3 import Optimize, Int, sat

def minutes_to_time_str(m):
    # m is the number of minutes past 9:00.
    hour = 9 + m // 60
    minute = m % 60
    return f"{hour}:{minute:02d}"

def main():
    opt = Optimize()

    # Define meeting time variables (in minutes since 9:00)
    carol_start = Int('carol_start')
    carol_end   = Int('carol_end')
    karen_start = Int('karen_start')
    karen_end   = Int('karen_end')
    rebecca_start = Int('rebecca_start')
    rebecca_end   = Int('rebecca_end')

    # Carol is at Sunset District from 10:15 (75) to 11:45 (165); meet for at least 30 minutes.
    opt.add(carol_start >= 75)
    opt.add(carol_end <= 165)
    opt.add(carol_end - carol_start >= 30)

    # Karen is at Bayview from 12:45 (225) to 15:00 (360); meet for at least 120 minutes.
    opt.add(karen_start >= 225)
    opt.add(karen_end <= 360)
    opt.add(karen_end - karen_start >= 120)

    # Rebecca is at Mission District from 11:30 (150) to 20:15 (675); meet for at least 120 minutes.
    opt.add(rebecca_start >= 150)
    opt.add(rebecca_end <= 675)
    opt.add(rebecca_end - rebecca_start >= 120)

    # Travel constraints:
    # Start at Union Square at 9:00 (0 minutes). We need to travel to each meeting location.
    # Travel time from Union Square to Sunset District (Carol) is 26 minutes.
    # (Although Carol's availability starts at 75, we add the travel requirement explicitly.)
    opt.add(carol_start >= 26)

    # After Carol's meeting (at Sunset District), travel to Karen at Bayview takes 22 minutes.
    opt.add(karen_start >= carol_end + 22)

    # After Karen's meeting (at Bayview), travel to Rebecca at Mission District takes 13 minutes.
    opt.add(rebecca_start >= karen_end + 13)

    # Objective: minimize the overall finish time (Rebecca's meeting end).
    opt.minimize(rebecca_end)

    if opt.check() == sat:
        m = opt.model()
        itinerary = []
        itinerary.append({
            "action": "meet",
            "location": "Sunset District",
            "person": "Carol",
            "start_time": minutes_to_time_str(m[carol_start].as_long()),
            "end_time": minutes_to_time_str(m[carol_end].as_long())
        })
        itinerary.append({
            "action": "meet",
            "location": "Bayview",
            "person": "Karen",
            "start_time": minutes_to_time_str(m[karen_start].as_long()),
            "end_time": minutes_to_time_str(m[karen_end].as_long())
        })
        itinerary.append({
            "action": "meet",
            "location": "Mission District",
            "person": "Rebecca",
            "start_time": minutes_to_time_str(m[rebecca_start].as_long()),
            "end_time": minutes_to_time_str(m[rebecca_end].as_long())
        })

        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()