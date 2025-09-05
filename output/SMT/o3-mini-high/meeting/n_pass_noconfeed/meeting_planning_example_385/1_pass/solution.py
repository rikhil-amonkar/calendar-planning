import json
from z3 import *

def main():
    # Create an Optimize solver to maximize the number of meetings
    opt = Optimize()

    # Boolean decision variables: whether to schedule a meeting with each friend
    jeffrey = Bool('jeffrey')
    john = Bool('john')
    steven = Bool('steven')
    barbara = Bool('barbara')

    # Integer variables for meeting start times (minutes after midnight)
    s_jeffrey = Int('s_jeffrey')
    s_john = Int('s_john')
    s_steven = Int('s_steven')
    s_barbara = Int('s_barbara')

    # Meeting durations (in minutes)
    dur_jeffrey = 105
    dur_john = 15
    dur_steven = 45
    dur_barbara = 30

    # Define travel times (in minutes) between locations
    travel = {
        ("Nob Hill", "Presidio"): 17,
        ("Nob Hill", "North Beach"): 8,
        ("Nob Hill", "Fisherman's Wharf"): 11,
        ("Nob Hill", "Pacific Heights"): 8,
        ("Presidio", "Nob Hill"): 18,
        ("Presidio", "North Beach"): 18,
        ("Presidio", "Fisherman's Wharf"): 19,
        ("Presidio", "Pacific Heights"): 11,
        ("North Beach", "Nob Hill"): 7,
        ("North Beach", "Presidio"): 17,
        ("North Beach", "Fisherman's Wharf"): 5,
        ("North Beach", "Pacific Heights"): 8,
        ("Fisherman's Wharf", "Nob Hill"): 11,
        ("Fisherman's Wharf", "Presidio"): 17,
        ("Fisherman's Wharf", "North Beach"): 6,
        ("Fisherman's Wharf", "Pacific Heights"): 12,
        ("Pacific Heights", "Nob Hill"): 8,
        ("Pacific Heights", "Presidio"): 11,
        ("Pacific Heights", "North Beach"): 9,
        ("Pacific Heights", "Fisherman's Wharf"): 13,
    }

    # Helper function to look up travel time between two given locations
    def tt(source, dest):
        return travel[(source, dest)]

    # The traveler arrives at Nob Hill at 9:00 (9*60 = 540 minutes).
    start_nobhill = 540

    # Add availability and reachability constraints for each meeting.
    # Meeting with Jeffrey:
    # Jeffrey is available at Presidio from 8:00 (480) to 10:00 (600).
    # To meet him for 105 minutes, the meeting must end by 600, i.e. start <= 600-105 = 495.
    # Also, if meeting, you must travel from Nob Hill to Presidio,
    # so the start must be at least 540 + tt("Nob Hill", "Presidio") = 540+17 = 557.
    opt.add(Implies(jeffrey, s_jeffrey >= 557))
    opt.add(Implies(jeffrey, s_jeffrey <= 600 - dur_jeffrey))  # s_jeffrey <= 495

    # Meeting with John:
    # John is available at Pacific Heights from 9:00 (540) to 13:30 (810).
    # The meeting must last at least 15 minutes so start <= 810-15 = 795.
    # If meeting, to go directly from Nob Hill to Pacific Heights: 540+tt("Nob Hill", "Pacific Heights") = 540+8 = 548.
    opt.add(Implies(john, s_john >= 548))
    opt.add(Implies(john, s_john <= 810 - dur_john))  # s_john <= 795

    # Meeting with Steven:
    # Steven is available at North Beach from 13:30 (810) to 22:00 (1320) for at least 45 minutes.
    # Direct travel from Nob Hill to North Beach: 540+tt("Nob Hill", "North Beach") = 540+8 = 548, but
    # availability gives a stronger lower bound of 810.
    opt.add(Implies(steven, s_steven >= 810))
    opt.add(Implies(steven, s_steven <= 1320 - dur_steven))  # s_steven <= 1275

    # Meeting with Barbara:
    # Barbara is available at Fisherman's Wharf from 18:00 (1080) to 21:30 (1290) for at least 30 minutes.
    # Direct travel from Nob Hill to Fisherman's Wharf: 540+tt("Nob Hill", "Fisherman's Wharf") = 540+11 = 551,
    # so use availability lower bound 1080.
    opt.add(Implies(barbara, s_barbara >= 1080))
    opt.add(Implies(barbara, s_barbara <= 1290 - dur_barbara))  # s_barbara <= 1260

    # Add ordering/travel constraints between meetings.
    # Since the available windows force an order (if scheduled) as:
    # Jeffrey (ends by 600) -> John (available until 13:30) -> Steven (starts at 13:30) -> Barbara (starts at 18:00)
    #
    # If a pair of meetings is scheduled, then the earlier meeting must finish (including its meeting time)
    # plus the travel time between the locations before the later meeting can start.
    #
    # Jeffrey must come before John, Steven, and Barbara if scheduled.
    opt.add(Implies(And(jeffrey, john), s_jeffrey + dur_jeffrey + tt("Presidio", "Pacific Heights") <= s_john))
    opt.add(Implies(And(jeffrey, steven), s_jeffrey + dur_jeffrey + tt("Presidio", "North Beach") <= s_steven))
    opt.add(Implies(And(jeffrey, barbara), s_jeffrey + dur_jeffrey + tt("Presidio", "Fisherman's Wharf") <= s_barbara))

    # John comes before Steven and Barbara.
    opt.add(Implies(And(john, steven), s_john + dur_john + tt("Pacific Heights", "North Beach") <= s_steven))
    opt.add(Implies(And(john, barbara), s_john + dur_john + tt("Pacific Heights", "Fisherman's Wharf") <= s_barbara))

    # Steven comes before Barbara.
    opt.add(Implies(And(steven, barbara), s_steven + dur_steven + tt("North Beach", "Fisherman's Wharf") <= s_barbara))

    # For a meeting that is the first scheduled meeting, it must be reachable directly from Nob Hill.
    # If John is scheduled and Jeffrey is not, then John is the first meeting.
    opt.add(Implies(And(john, Not(jeffrey)), s_john >= start_nobhill + tt("Nob Hill", "Pacific Heights")))
    # Similarly for Steven if neither Jeffrey nor John are scheduled.
    opt.add(Implies(And(steven, Not(jeffrey), Not(john)), s_steven >= start_nobhill + tt("Nob Hill", "North Beach")))
    # And for Barbara if none of the others are scheduled.
    opt.add(Implies(And(barbara, Not(jeffrey), Not(john), Not(steven)), s_barbara >= start_nobhill + tt("Nob Hill", "Fisherman's Wharf")))

    # Set the optimization objective: maximize the number of meetings scheduled.
    meeting_count = Sum([If(jeffrey, 1, 0),
                           If(john, 1, 0),
                           If(steven, 1, 0),
                           If(barbara, 1, 0)])
    opt.maximize(meeting_count)

    # Check for an optimal solution
    if opt.check() == sat:
        model = opt.model()

        # Build the itinerary list for scheduled meetings.
        # Each meeting is represented as a tuple: (person, location, start time, end time)
        meetings = []
        if is_true(model.evaluate(jeffrey)):
            start = model.evaluate(s_jeffrey).as_long()
            end = start + dur_jeffrey
            meetings.append(("Jeffrey", "Presidio", start, end))
        if is_true(model.evaluate(john)):
            start = model.evaluate(s_john).as_long()
            end = start + dur_john
            meetings.append(("John", "Pacific Heights", start, end))
        if is_true(model.evaluate(steven)):
            start = model.evaluate(s_steven).as_long()
            end = start + dur_steven
            meetings.append(("Steven", "North Beach", start, end))
        if is_true(model.evaluate(barbara)):
            start = model.evaluate(s_barbara).as_long()
            end = start + dur_barbara
            meetings.append(("Barbara", "Fisherman's Wharf", start, end))

        # Sort the meetings by their start time
        meetings.sort(key=lambda m: m[2])

        # Helper function to convert minutes into H:MM (24-hour) format.
        def format_time(minutes):
            hr = minutes // 60
            mn = minutes % 60
            return f"{hr}:{mn:02d}"

        itinerary = []
        for person, location, start_time, end_time in meetings:
            itinerary.append({
                "action": "meet",
                "location": location,
                "person": person,
                "start_time": format_time(start_time),
                "end_time": format_time(end_time)
            })

        # Output the result as a JSON-formatted dictionary.
        output = {"itinerary": itinerary}
        print(json.dumps(output))
    else:
        # No schedule found.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()