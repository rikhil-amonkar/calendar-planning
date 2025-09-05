import json
from z3 import *

def minute_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours}:{minutes:02d}"

def main():
    # Create an Optimize object so that we “compute” a schedule from our constraints.
    solver = Optimize()

    # Define integer variables for the meeting start times (minutes after midnight)
    S_daniel    = Int('S_daniel')
    S_margaret  = Int('S_margaret')
    S_charles   = Int('S_charles')
    S_stephanie = Int('S_stephanie')
    
    # Boolean variable: if True then morning order is Daniel then Margaret,
    # if False then the order is Margaret then Daniel.
    morning_first = Bool('morning_first')
    
    # Meeting durations (in minutes)
    dur_daniel    = 15
    dur_margaret  = 30
    dur_charles   = 90
    dur_stephanie = 90

    # Starting location: Sunset District at 9:00AM (9*60 = 540)
    start_time = 540

    # Travel times (in minutes) between locations
    travel = {
        "Sunset District": {"Alamo Square": 17, "Russian Hill": 24, "Golden Gate Park": 11, "Mission District": 24},
        "Alamo Square":    {"Sunset District": 16, "Russian Hill": 13, "Golden Gate Park": 9,  "Mission District": 10},
        "Russian Hill":    {"Sunset District": 23, "Alamo Square": 15, "Golden Gate Park": 21, "Mission District": 16},
        "Golden Gate Park":{"Sunset District": 10, "Alamo Square": 10, "Russian Hill": 19, "Mission District": 17},
        "Mission District": {"Sunset District": 24, "Alamo Square": 11, "Russian Hill": 15, "Golden Gate Park": 17}
    }

    # Friend availability windows and meeting requirements:
    # Times are in minutes from midnight.
    avail = {
        "Charles":   {"location": "Alamo Square",   "start": 18*60,     "end": 20*60+45, "min_duration": 90},
        "Margaret":  {"location": "Russian Hill",   "start": 9*60,      "end": 16*60,    "min_duration": 30},
        "Daniel":    {"location": "Golden Gate Park","start": 8*60,      "end": 13*60+30, "min_duration": 15},
        "Stephanie": {"location": "Mission District", "start": 20*60+30,  "end": 22*60,    "min_duration": 90}
    }

    # EVENING BLOCK CONSTRAINTS
    # Charles must be met at Alamo Square between 18:00 and 20:45 for at least 90 minutes.
    solver.add(S_charles >= avail["Charles"]["start"])        # 18:00 = 1080
    solver.add(S_charles + dur_charles <= avail["Charles"]["end"])  # Ends by or before 20:45 (1245)
    # To allow transition to Stephanie, force S_charles to be no later than 1230-100 = 1130.
    solver.add(S_charles <= 1230 - 100)
    
    # Stephanie’s meeting is fixed to start at her available start time (20:30) so that a 90-minute meeting exactly fills her window.
    solver.add(S_stephanie == avail["Stephanie"]["start"])
    # Ensure sufficient travel time from Charles (Alamo Square) to Stephanie (Mission District) after a 90-min meeting.
    solver.add(S_stephanie >= S_charles + dur_charles + travel[avail["Charles"]["location"]][avail["Stephanie"]["location"]])
    
    # MORNING BLOCK CONSTRAINTS (two possible orders)
    # Option 1: morning_first == True means schedule Daniel first and then Margaret.
    solver.add(Implies(morning_first,
        S_daniel >= start_time + travel["Sunset District"][avail["Daniel"]["location"]]
    ))
    solver.add(Implies(morning_first,
        S_daniel >= avail["Daniel"]["start"]
    ))
    solver.add(Implies(morning_first,
        S_daniel + dur_daniel <= avail["Daniel"]["end"]
    ))
    # Daniel then Margaret: Margaret must start after Daniel’s meeting plus travel time from Golden Gate Park to Russian Hill.
    solver.add(Implies(morning_first,
        S_margaret >= S_daniel + dur_daniel + travel[avail["Daniel"]["location"]][avail["Margaret"]["location"]]
    ))
    solver.add(Implies(morning_first,
        S_margaret >= start_time + travel["Sunset District"][avail["Margaret"]["location"]]
    ))
    solver.add(Implies(morning_first,
        S_margaret + dur_margaret <= avail["Margaret"]["end"]
    ))
    # To ensure a timely transfer to Charles, Margaret must finish early enough.
    solver.add(Implies(morning_first,
        S_margaret <= avail["Charles"]["start"] - (dur_margaret + travel["Russian Hill"][avail["Charles"]["location"]])
    ))
    solver.add(Implies(morning_first,
        S_charles >= S_margaret + dur_margaret + travel[avail["Margaret"]["location"]][avail["Charles"]["location"]]
    ))

    # Option 2: morning_first == False means schedule Margaret first then Daniel.
    solver.add(Implies(Not(morning_first),
        S_margaret >= start_time + travel["Sunset District"][avail["Margaret"]["location"]]
    ))
    solver.add(Implies(Not(morning_first),
        S_margaret >= avail["Margaret"]["start"]
    ))
    solver.add(Implies(Not(morning_first),
        S_margaret + dur_margaret <= avail["Margaret"]["end"]
    ))
    # Also, Margaret must not be too late so that Daniel (meeting at Golden Gate Park) can meet before his window closes.
    solver.add(Implies(Not(morning_first),
        S_margaret <= (avail["Daniel"]["end"] - dur_daniel) - (avail["Margaret"]["min_duration"] + travel[avail["Margaret"]["location"]][avail["Daniel"]["location"]])
    ))
    solver.add(Implies(Not(morning_first),
        S_daniel >= S_margaret + dur_margaret + travel[avail["Margaret"]["location"]][avail["Daniel"]["location"]]
    ))
    solver.add(Implies(Not(morning_first),
        S_daniel >= avail["Daniel"]["start"]
    ))
    solver.add(Implies(Not(morning_first),
        S_daniel + dur_daniel <= avail["Daniel"]["end"]
    ))
    solver.add(Implies(Not(morning_first),
        S_charles >= S_daniel + dur_daniel + travel[avail["Daniel"]["location"]][avail["Charles"]["location"]]
    ))
    
    # Solve the constraints
    if solver.check() == sat:
        m = solver.model()
        daniel_start    = m[S_daniel].as_long()
        margaret_start  = m[S_margaret].as_long()
        charles_start   = m[S_charles].as_long()
        stephanie_start = m[S_stephanie].as_long()  # This should be 1230

        itinerary = []
        itinerary.append({
            "action": "meet",
            "location": avail["Daniel"]["location"],
            "person": "Daniel",
            "start_time": minute_to_time(daniel_start),
            "end_time": minute_to_time(daniel_start + dur_daniel)
        })
        itinerary.append({
            "action": "meet",
            "location": avail["Margaret"]["location"],
            "person": "Margaret",
            "start_time": minute_to_time(margaret_start),
            "end_time": minute_to_time(margaret_start + dur_margaret)
        })
        itinerary.append({
            "action": "meet",
            "location": avail["Charles"]["location"],
            "person": "Charles",
            "start_time": minute_to_time(charles_start),
            "end_time": minute_to_time(charles_start + dur_charles)
        })
        itinerary.append({
            "action": "meet",
            "location": avail["Stephanie"]["location"],
            "person": "Stephanie",
            "start_time": minute_to_time(stephanie_start),
            "end_time": minute_to_time(stephanie_start + dur_stephanie)
        })
        
        # Order events by start time
        itinerary.sort(key=lambda x: int(x["start_time"].split(":")[0]) * 60 + int(x["start_time"].split(":")[1]))
        schedule = {"itinerary": itinerary}
        print(json.dumps(schedule, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()