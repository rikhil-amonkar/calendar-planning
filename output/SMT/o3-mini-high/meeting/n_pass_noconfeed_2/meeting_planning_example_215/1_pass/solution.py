import json
from z3 import *

def format_time(t):
    # t is an integer representing minutes from midnight.
    h = t // 60
    m = t % 60
    return f"{h}:{m:02d}"

def main():
    # Create an Optimize solver instance.
    opt = Optimize()

    # Define the starting time (arrival at Bayview at 9:00AM = 9*60 = 540 minutes).
    start_time = 540

    # Travel times (in minutes)
    # These will be used depending on which meeting was last.
    travel_Bayview_Fisher = 25
    travel_Bayview_Embar = 19
    travel_Bayview_Richmond = 25
    travel_Fisher_Embar = 8
    travel_Fisher_Richmond = 18
    travel_Embar_Richmond = 21

    # Define meeting time variables for each friend, in minutes from midnight.
    s_jason = Int('s_jason')     # start time for Jason meeting at Fisherman's Wharf
    e_jason = Int('e_jason')     # end time for Jason meeting

    s_jessica = Int('s_jessica') # start time for Jessica meeting at Embarcadero
    e_jessica = Int('e_jessica') # end time for Jessica meeting

    s_sandra = Int('s_sandra')   # start time for Sandra meeting at Richmond District
    e_sandra = Int('e_sandra')   # end time for Sandra meeting

    # Define Boolean flags indicating whether to schedule a meeting with each friend.
    meet_jason   = Bool('meet_jason')
    meet_jessica = Bool('meet_jessica')
    meet_sandra  = Bool('meet_sandra')

    # Availability and minimum meeting duration constraints.
    # Jason is available from 16:00 (960) to 16:45 (1005), need at least 30 minutes.
    opt.add(Implies(meet_jason, s_jason >= 960))
    opt.add(Implies(meet_jason, e_jason <= 1005))
    opt.add(Implies(meet_jason, e_jason - s_jason >= 30))
    opt.add(Implies(meet_jason, s_jason >= start_time + travel_Bayview_Fisher))  # Travel from Bayview

    # Jessica is available from 16:45 (1005) to 19:00 (1140), need at least 30 minutes.
    opt.add(Implies(meet_jessica, s_jessica >= 1005))
    opt.add(Implies(meet_jessica, e_jessica <= 1140))
    opt.add(Implies(meet_jessica, e_jessica - s_jessica >= 30))
    # Travel to Jessica: if Jason met then from Fisherman's Wharf, else from Bayview.
    opt.add(Implies(meet_jessica,
                    s_jessica >= If(meet_jason, e_jason + travel_Fisher_Embar, start_time + travel_Bayview_Embar)))

    # Sandra is available from 18:30 (1110) to 21:45 (1305), need at least 120 minutes.
    opt.add(Implies(meet_sandra, s_sandra >= 1110))
    opt.add(Implies(meet_sandra, e_sandra <= 1305))
    opt.add(Implies(meet_sandra, e_sandra - s_sandra >= 120))
    # Travel to Sandra: if Jessica met then from Embarcadero,
    # else if Jason met then from Fisherman's Wharf,
    # else from Bayview.
    opt.add(Implies(meet_sandra,
                    s_sandra >= If(meet_jessica, e_jessica + travel_Embar_Richmond,
                                   If(meet_jason, e_jason + travel_Fisher_Richmond, start_time + travel_Bayview_Richmond))))

    # If a meeting is not scheduled, fix its start and end times to 0.
    opt.add(Implies(Not(meet_jason), And(s_jason == 0, e_jason == 0)))
    opt.add(Implies(Not(meet_jessica), And(s_jessica == 0, e_jessica == 0)))
    opt.add(Implies(Not(meet_sandra), And(s_sandra == 0, e_sandra == 0)))

    # Basic sanity: if meeting is scheduled, start time must be before end time.
    opt.add(Implies(meet_jason, s_jason < e_jason))
    opt.add(Implies(meet_jessica, s_jessica < e_jessica))
    opt.add(Implies(meet_sandra, s_sandra < e_sandra))

    # Objective: maximize the number of meetings.
    num_meetings = If(meet_jason, 1, 0) + If(meet_jessica, 1, 0) + If(meet_sandra, 1, 0)
    opt.maximize(num_meetings)

    # Check if a solution exists and extract it.
    if opt.check() == sat:
        m = opt.model()

        itinerary = []

        # Build a list of scheduled meetings with their computed times and locations.
        meetings = []
        if m.evaluate(meet_jason):
            start_val = m.evaluate(s_jason).as_long()
            end_val = m.evaluate(e_jason).as_long()
            meetings.append((start_val, {
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Jason",
                "start_time": format_time(start_val),
                "end_time": format_time(end_val)
            }))
        if m.evaluate(meet_jessica):
            start_val = m.evaluate(s_jessica).as_long()
            end_val = m.evaluate(e_jessica).as_long()
            meetings.append((start_val, {
                "action": "meet",
                "location": "Embarcadero",
                "person": "Jessica",
                "start_time": format_time(start_val),
                "end_time": format_time(end_val)
            }))
        if m.evaluate(meet_sandra):
            start_val = m.evaluate(s_sandra).as_long()
            end_val = m.evaluate(e_sandra).as_long()
            meetings.append((start_val, {
                "action": "meet",
                "location": "Richmond District",
                "person": "Sandra",
                "start_time": format_time(start_val),
                "end_time": format_time(end_val)
            }))

        # Sort the meetings by start time.
        meetings.sort(key=lambda x: x[0])
        itinerary = [entry for _, entry in meetings]

        # Prepare the output JSON.
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        # If no schedule is feasible, output an empty itinerary.
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()