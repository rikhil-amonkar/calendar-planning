from z3 import Optimize, Int, sat
import json

def format_time(minutes):
    h = minutes // 60
    m = minutes % 60
    # Format hour without leading zero and minutes with two digits
    return f"{h}:{m:02d}"

def main():
    # Input parameters (all times in minutes from midnight)
    # You arrive at Russian Hill at 9:00 AM = 9*60 = 540 minutes
    ARRIVAL_RH = 9 * 60  # 540
    
    # Travel times in minutes
    TRAVEL_RH_TO_RICHMOND = 14
    TRAVEL_RICHMOND_TO_RH = 13

    # Daniel's availability at Richmond District: 19:00 to 20:15
    DANIEL_AVAILABLE_START = 19 * 60      # 1140 minutes (19:00)
    DANIEL_AVAILABLE_END = 20 * 60 + 15     # 1215 minutes (20:15)
    
    # Meeting duration constraint: minimum of 75 minutes
    MIN_MEETING_DURATION = 75

    # Create an SMT optimization model
    opt = Optimize()
    
    # Define SMT variables for meeting start and end times (in minutes after midnight)
    meeting_start = Int("meeting_start")
    meeting_end = Int("meeting_end")
    # Define departure time from Russian Hill
    departure_rh = Int("departure_rh")
    
    # Constraints:
    # You cannot depart Russian Hill before arriving.
    opt.add(departure_rh >= ARRIVAL_RH)
    
    # You must account for travel from Russian Hill to Richmond District
    opt.add(meeting_start >= departure_rh + TRAVEL_RH_TO_RICHMOND)
    
    # You must meet Daniel within his availability window
    opt.add(meeting_start >= DANIEL_AVAILABLE_START)
    opt.add(meeting_end <= DANIEL_AVAILABLE_END)
    
    # Meeting duration must be at least the minimum required
    opt.add(meeting_end - meeting_start >= MIN_MEETING_DURATION)
    
    # (Optional) You could require that after the meeting you travel back to Russian Hill,
    # ensuring that the return trip is feasible. For example:
    # return_time = meeting_end + TRAVEL_RICHMOND_TO_RH
    # Here, no further constraint is applied as the itinerary focuses on the meeting.
    
    # Objective: Maximize the meeting duration (this in effect will schedule the meeting
    # to use as much of Daniel's available time as possible).
    meeting_duration = meeting_end - meeting_start
    opt.maximize(meeting_duration)
    
    # Check for a solution that satisfies the constraints
    if opt.check() == sat:
        model = opt.model()
        scheduled_meeting_start = model[meeting_start].as_long()
        scheduled_meeting_end = model[meeting_end].as_long()
        
        # Prepare the itinerary JSON structure
        itinerary = [{
            "action": "meet",
            "location": "Richmond District",
            "person": "Daniel",
            "start_time": format_time(scheduled_meeting_start),
            "end_time": format_time(scheduled_meeting_end)
        }]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        # In the unlikely case no schedule can be found, output an error message in JSON.
        print(json.dumps({"error": "No valid schedule found."}))

if __name__ == "__main__":
    main()