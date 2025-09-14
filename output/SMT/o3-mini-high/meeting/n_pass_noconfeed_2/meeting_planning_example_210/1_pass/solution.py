from z3 import *
import json

def minutes_to_time(m):
    h = m // 60
    minute = m % 60
    return f"{h}:{minute:02d}"

def main():
    # Travel times in minutes between locations
    travel = {
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "Richmond District"): 18,
        ("Fisherman's Wharf", "Financial District"): 11,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Richmond District"): 7,
        ("Presidio", "Financial District"): 23,
        ("Richmond District", "Fisherman's Wharf"): 18,
        ("Richmond District", "Presidio"): 7,
        ("Richmond District", "Financial District"): 22,
        ("Financial District", "Fisherman's Wharf"): 10,
        ("Financial District", "Presidio"): 22,
        ("Financial District", "Richmond District"): 21,
    }

    # Create an Optimize object for minimizing the overall finish time.
    opt = Optimize()

    # Meeting start time variables (in minutes from midnight)
    s_Emily = Int("s_Emily")
    s_Joseph = Int("s_Joseph")
    s_Melissa = Int("s_Melissa")

    # Order variables: position in the itinerary (1, 2, or 3)
    o_Emily = Int("o_Emily")
    o_Joseph = Int("o_Joseph")
    o_Melissa = Int("o_Melissa")

    # Meeting durations in minutes
    d_Emily = 105
    d_Joseph = 120
    d_Melissa = 75

    # Availability windows (in minutes from midnight)
    # Emily at Presidio: 16:15 (975) to 21:00 (1260)
    # Joseph at Richmond District: 17:15 (1035) to 22:00 (1320)
    # Melissa at Financial District: 15:45 (945) to 21:45 (1305)
    opt.add(s_Emily >= 975, s_Emily + d_Emily <= 1260)
    opt.add(s_Joseph >= 1035, s_Joseph + d_Joseph <= 1320)
    opt.add(s_Melissa >= 945, s_Melissa + d_Melissa <= 1305)

    # Order values must be between 1 and 3 and all distinct
    opt.add(o_Emily >= 1, o_Emily <= 3)
    opt.add(o_Joseph >= 1, o_Joseph <= 3)
    opt.add(o_Melissa >= 1, o_Melissa <= 3)
    opt.add(Distinct(o_Emily, o_Joseph, o_Melissa))

    # For any two meetings, enforce sequential constraints.
    # If meeting A comes before meeting B then:
    #   s_B >= s_A + duration_A + travel_time(from A's location to B's location)
    # Locations:
    #   Emily -> "Presidio"
    #   Joseph -> "Richmond District"
    #   Melissa -> "Financial District"
    #
    # Constraint between Melissa and Emily:
    opt.add(If(o_Melissa < o_Emily,
               s_Emily >= s_Melissa + d_Melissa + travel[("Financial District", "Presidio")],
               s_Melissa >= s_Emily + d_Emily + travel[("Presidio", "Financial District")]))
    # Constraint between Melissa and Joseph:
    opt.add(If(o_Melissa < o_Joseph,
               s_Joseph >= s_Melissa + d_Melissa + travel[("Financial District", "Richmond District")],
               s_Melissa >= s_Joseph + d_Joseph + travel[("Richmond District", "Financial District")]))
    # Constraint between Emily and Joseph:
    opt.add(If(o_Emily < o_Joseph,
               s_Joseph >= s_Emily + d_Emily + travel[("Presidio", "Richmond District")],
               s_Emily >= s_Joseph + d_Joseph + travel[("Richmond District", "Presidio")]))

    # For the first meeting, you start from Fisherman's Wharf at 9:00 (540 minutes).
    # So if a meeting is scheduled first (order == 1), ensure you have time to travel there.
    opt.add(Implies(o_Emily == 1, s_Emily >= 540 + travel[("Fisherman's Wharf", "Presidio")]))
    opt.add(Implies(o_Joseph == 1, s_Joseph >= 540 + travel[("Fisherman's Wharf", "Richmond District")]))
    opt.add(Implies(o_Melissa == 1, s_Melissa >= 540 + travel[("Fisherman's Wharf", "Financial District")]))

    # Define an overall finish time variable (when the last meeting ends).
    finish_time = Int("finish_time")
    opt.add(finish_time >= s_Emily + d_Emily)
    opt.add(finish_time >= s_Joseph + d_Joseph)
    opt.add(finish_time >= s_Melissa + d_Melissa)

    # Objective: minimize the overall finish time.
    opt.minimize(finish_time)

    if opt.check() == sat:
        m = opt.model()
        # Extract each meeting's details: (person, location, start time, duration, order)
        meetings = [
            ("Emily", "Presidio", m[s_Emily].as_long(), d_Emily, m[o_Emily].as_long()),
            ("Joseph", "Richmond District", m[s_Joseph].as_long(), d_Joseph, m[o_Joseph].as_long()),
            ("Melissa", "Financial District", m[s_Melissa].as_long(), d_Melissa, m[o_Melissa].as_long()),
        ]
        # Sort the meetings based on the order variable
        meetings.sort(key=lambda x: x[4])
        itinerary = []
        for person, location, start, duration, order in meetings:
            meeting = {
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": minutes_to_time(start),
                "end_time": minutes_to_time(start + duration)
            }
            itinerary.append(meeting)
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()