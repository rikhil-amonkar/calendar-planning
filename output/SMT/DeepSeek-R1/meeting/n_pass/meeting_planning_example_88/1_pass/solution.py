import json
from z3 import *

def main():
    # Convert time constraints to minutes since midnight
    start_of_day = 9 * 60  # 9:00 AM
    joshua_available_start = 20 * 60 + 45  # 20:45 (8:45 PM)
    joshua_available_end = 21 * 60 + 45    # 21:45 (9:45 PM)
    min_meeting_duration = 15
    travel_time_to_park = 11

    # Create Z3 integer variables
    departure_from_sunset = Int('departure_from_sunset')  # Departure time from Sunset District (minutes)
    meeting_start = Int('meeting_start')                  # Meeting start time (minutes)

    # Initialize solver
    solver = Solver()

    # Constraints:
    # 1. Departure must be after or at 9:00 AM
    solver.add(departure_from_sunset >= start_of_day)
    
    # 2. Arrival at Golden Gate Park (departure + travel time) must be before or at meeting start
    solver.add(departure_from_sunset + travel_time_to_park <= meeting_start)
    
    # 3. Meeting must start during Joshua's availability
    solver.add(meeting_start >= joshua_available_start)
    
    # 4. Meeting must end by 9:45 PM (meeting start + 15 minutes <= 21:45)
    solver.add(meeting_start + min_meeting_duration <= joshua_available_end)

    # Check for a valid solution
    if solver.check() == sat:
        model = solver.model()
        meeting_start_minutes = model.eval(meeting_start).as_long()
        meeting_end_minutes = meeting_start_minutes + min_meeting_duration

        # Format times to HH:MM
        def format_time(minutes):
            hours = minutes // 60
            mins = minutes % 60
            return f"{hours:02d}:{mins:02d}"

        meeting_start_str = format_time(meeting_start_minutes)
        meeting_end_str = format_time(meeting_end_minutes)

        # Create itinerary entry
        itinerary = [{
            "action": "meet",
            "person": "Joshua",
            "start_time": meeting_start_str,
            "end_time": meeting_end_str
        }]
        
        # Output as JSON
        print(json.dumps({"itinerary": itinerary}))
    else:
        # No solution found (though one should exist)
        print(json.dumps({"itinerary": []}))

if __name__ == "__main__":
    main()