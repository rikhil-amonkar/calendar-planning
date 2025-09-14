from z3 import Optimize, Int, sat
import json

def minutes_to_time(minutes):
    # Convert minutes since midnight to "H:MM" 24-hour format (no leading zero for hour)
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an optimizer instance
    opt = Optimize()
    
    # Define SMT variables (times are in minutes since midnight)
    depart_time = Int('depart_time')         # time to depart from Sunset District
    meeting_start = Int('meeting_start')       # meeting start time at Golden Gate Park (for Joshua)
    meeting_end = Int('meeting_end')           # meeting end time at Golden Gate Park (for Joshua)
    
    # Constants
    arrival_sunset = 9 * 60                  # 9:00 AM -> 540 minutes
    travel_to_gp = 11                        # travel time from Sunset District to Golden Gate Park (in minutes)
    travel_back = 10                         # travel time from Golden Gate Park to Sunset District (in minutes)
    joshua_available_start = 20 * 60 + 45      # Joshua available from 8:45 PM -> 1245 minutes
    joshua_available_end = 21 * 60 + 45        # Joshua available until 9:45 PM -> 1305 minutes
    min_meeting_duration = 15                # minimum meeting duration (in minutes)
    
    # Add constraints for the Joshua meeting at Golden Gate Park
    opt.add(depart_time >= arrival_sunset)                               # Must depart no earlier than arrival at Sunset District.
    opt.add(meeting_start >= joshua_available_start)                       # Meeting cannot start before Joshua is available.
    opt.add(meeting_end <= joshua_available_end)                           # Meeting must end by Joshua's availability.
    opt.add(meeting_end - meeting_start >= min_meeting_duration)           # Must meet Joshua for at least 15 minutes.
    opt.add(meeting_start >= depart_time + travel_to_gp)                   # Arrival at Golden Gate Park happens before meeting starts.
    
    # Set optimization objective:
    # Primary objective: maximize Joshua's meeting duration.
    meeting_duration = meeting_end - meeting_start
    opt.maximize(meeting_duration)
    
    # Secondary objective: minimize the departure time to allow for potential additional meetings.
    opt.minimize(depart_time)
    
    # Solve the constraints
    if opt.check() == sat:
        model = opt.model()
        dep_val = model[depart_time].as_long() if model[depart_time] is not None else arrival_sunset
        ms_val = model[meeting_start].as_long() if model[meeting_start] is not None else joshua_available_start
        me_val = model[meeting_end].as_long() if model[meeting_end] is not None else joshua_available_end
        
        # Compute return time after Joshua's meeting
        return_time = me_val + travel_back
        
        # Construct first meeting: meet Joshua at Golden Gate Park.
        joshua_meeting = {
            "action": "meet",
            "location": "Golden Gate Park",
            "person": "Joshua",
            "start_time": minutes_to_time(ms_val),
            "end_time": minutes_to_time(me_val)
        }
        
        # For demonstration, add a second meeting in Sunset District with another friend (Alex)
        # Assume Alex is available upon your return and schedule a 30-minute meeting.
        alex_meeting_duration = 30
        alex_meeting = {
            "action": "meet",
            "location": "Sunset District",
            "person": "Alex",
            "start_time": minutes_to_time(return_time),
            "end_time": minutes_to_time(return_time + alex_meeting_duration)
        }
        
        itinerary = {
            "itinerary": [joshua_meeting, alex_meeting]
        }
        
        print(json.dumps(itinerary, indent=2))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()