import json
from z3 import Optimize, Int, sat

def convert_minutes_to_time(minutes):
    # Our time variables are minutes past 9:00.
    # So convert minutes past 9:00 into an absolute time in 24-hour format.
    total = 9 * 60 + minutes
    hr = total // 60
    mn = total % 60
    return f"{hr}:{mn:02d}"

def main():
    opt = Optimize()

    # Define integer decision variables for meeting start and end times
    # Times are measured in minutes after 9:00 AM.
    matthew_start = Int("matthew_start")
    matthew_end   = Int("matthew_end")
    robert_start  = Int("robert_start")
    robert_end    = Int("robert_end")
    joseph_start  = Int("joseph_start")
    joseph_end    = Int("joseph_end")
    sarah_start   = Int("sarah_start")
    sarah_end     = Int("sarah_end")
    patricia_start= Int("patricia_start")
    patricia_end  = Int("patricia_end")

    # Travel times in minutes between locations we will use in the scheduling order.
    # The meeting order is fixed as:
    # Start at Golden Gate Park -> Matthew (Marina District) -> Robert (Union Square)
    # -> Joseph (Financial District) -> Sarah (Haight-Ashbury) -> Patricia (Sunset District)
    travel = {
        # From Golden Gate Park to first meeting (Marina District)
        ("Golden Gate Park", "Marina District"): 16,
        ("Marina District", "Union Square"): 16,
        ("Union Square", "Financial District"): 9,
        ("Financial District", "Haight-Ashbury"): 19,
        ("Haight-Ashbury", "Sunset District"): 15,
    }

    # Availability windows and minimum meeting durations (in minutes)
    # All times are represented as minutes after 9:00.
    # Matthew: Available 9:15 (15) to 12:00 (180), min 15 minutes. (Location: Marina District)
    # Robert:  Available 10:15 (75) to 21:45 (765), min 15 minutes. (Location: Union Square)
    # Joseph:  Available 14:15 (315) to 18:45 (585), min 30 minutes. (Location: Financial District)
    # Sarah:   Available 17:00 (480) to 21:30 (750), min 105 minutes. (Location: Haight-Ashbury)
    # Patricia:Available 17:00 (480) to 19:45 (645), min 45 minutes. (Location: Sunset District)

    # Constraint for Matthew meeting (in Marina District)
    # We start at Golden Gate Park at 9:00; travel time to Marina District is 16 minutes.
    # Also, Matthew is available starting at 9:15 (15 min past 9:00).
    # Therefore, the meeting can start no earlier than max(16, 15) = 16.
    opt.add(matthew_start >= 16)
    opt.add(matthew_end >= matthew_start + 15)
    opt.add(matthew_end <= 180)

    # Constraint for Robert meeting (in Union Square)
    # Travel from Marina District to Union Square takes 16 minutes.
    opt.add(robert_start >= matthew_end + travel[("Marina District", "Union Square")])
    # Robert is available starting at 10:15 (75 minutes after 9:00).
    opt.add(robert_start >= 75)
    opt.add(robert_end >= robert_start + 15)
    opt.add(robert_end <= 765)

    # Constraint for Joseph meeting (in Financial District)
    # Travel from Union Square to Financial District takes 9 minutes.
    opt.add(joseph_start >= robert_end + travel[("Union Square", "Financial District")])
    # Joseph is available starting at 14:15 (315 minutes after 9:00).
    opt.add(joseph_start >= 315)
    opt.add(joseph_end >= joseph_start + 30)
    opt.add(joseph_end <= 585)

    # Constraint for Sarah meeting (in Haight-Ashbury)
    # Travel from Financial District to Haight-Ashbury takes 19 minutes.
    opt.add(sarah_start >= joseph_end + travel[("Financial District", "Haight-Ashbury")])
    # Sarah is available starting at 17:00 (480 minutes after 9:00).
    opt.add(sarah_start >= 480)
    opt.add(sarah_end >= sarah_start + 105)
    opt.add(sarah_end <= 750)

    # Constraint for Patricia meeting (in Sunset District)
    # Travel from Haight-Ashbury to Sunset District takes 15 minutes.
    opt.add(patricia_start >= sarah_end + travel[("Haight-Ashbury", "Sunset District")])
    # Patricia is available starting at 17:00 (480 minutes after 9:00).
    opt.add(patricia_start >= 480)
    opt.add(patricia_end >= patricia_start + 45)
    opt.add(patricia_end <= 645)

    # Set an objective: minimize the finish time of the overall schedule (i.e. Patricia's end time).
    opt.minimize(patricia_end)

    if opt.check() == sat:
        m = opt.model()
        itinerary = [
            {
                "action": "meet",
                "location": "Marina District",
                "person": "Matthew",
                "start_time": convert_minutes_to_time(m[matthew_start].as_long()),
                "end_time": convert_minutes_to_time(m[matthew_end].as_long())
            },
            {
                "action": "meet",
                "location": "Union Square",
                "person": "Robert",
                "start_time": convert_minutes_to_time(m[robert_start].as_long()),
                "end_time": convert_minutes_to_time(m[robert_end].as_long())
            },
            {
                "action": "meet",
                "location": "Financial District",
                "person": "Joseph",
                "start_time": convert_minutes_to_time(m[joseph_start].as_long()),
                "end_time": convert_minutes_to_time(m[joseph_end].as_long())
            },
            {
                "action": "meet",
                "location": "Haight-Ashbury",
                "person": "Sarah",
                "start_time": convert_minutes_to_time(m[sarah_start].as_long()),
                "end_time": convert_minutes_to_time(m[sarah_end].as_long())
            },
            {
                "action": "meet",
                "location": "Sunset District",
                "person": "Patricia",
                "start_time": convert_minutes_to_time(m[patricia_start].as_long()),
                "end_time": convert_minutes_to_time(m[patricia_end].as_long())
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()