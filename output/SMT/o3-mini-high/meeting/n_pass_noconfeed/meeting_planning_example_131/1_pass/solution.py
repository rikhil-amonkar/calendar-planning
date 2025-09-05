import json
from z3 import Optimize, Int, sat

# Helper function to convert minutes (offset from 9:00) into a 24-hour time string.
def format_time(minutes_offset):
    total_minutes = 9 * 60 + minutes_offset
    hour = total_minutes // 60
    minute = total_minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an optimizer instance from Z3.
    opt = Optimize()
    
    # Define integer variables representing times in minutes after 9:00AM.
    # For Jason's meeting at Presidio.
    tj_start = Int('tj_start')  # Start time of meeting with Jason (in minutes after 9:00)
    tj_end = Int('tj_end')      # End time of meeting with Jason
    # For Kenneth's meeting at Marina District.
    tk_start = Int('tk_start')  # Start time of meeting with Kenneth
    tk_end = Int('tk_end')      # End time of meeting with Kenneth

    # Input parameters for travel times (in minutes)
    travel_PH_to_Presidio = 11       # Pacific Heights -> Presidio
    travel_Presidio_to_Marina = 10     # Presidio -> Marina District

    # Meeting availability windows (in minutes after 9:00)
    # Jason: Available from 10:00 (60) to 16:15 (435). However, to allow travel to Kenneth,
    # we must finish Jason’s meeting by 16:00 - travel time - required meeting time buffer.
    jason_available_start = 60
    jason_available_end = 435  # Jason is available until 16:15, but our chaining forces an earlier finish.
    required_jason_duration = 90

    # Kenneth: Available from 15:30 (390) to 16:45 (465)
    kenneth_available_start = 390
    kenneth_available_end = 465
    required_kenneth_duration = 45

    # Since we start at Pacific Heights at 9:00, after traveling to Presidio,
    # we must arrive at or after (9:00 + travel_PH_to_Presidio). 
    # Jason is available only from 10:00, so effectively, the meeting with Jason 
    # can start no earlier than 10:00.
    opt.add(tj_start >= jason_available_start)

    # We must meet Jason for at least the minimum duration.
    opt.add(tj_end - tj_start >= required_jason_duration)
    
    # Even though Jason is available until 16:15 (435 minutes after 9:00),
    # we must allow enough time to travel from Presidio to Marina District (10 minutes)
    # and hold a minimum 45 minute meeting with Kenneth.
    # That is, tj_end + travel_Presidio_to_Marina + required_kenneth_duration <= kenneth_available_end.
    opt.add(tj_end + travel_Presidio_to_Marina + required_kenneth_duration <= kenneth_available_end)
    # This implies:
    #   tj_end <= kenneth_available_end - travel_Presidio_to_Marina - required_kenneth_duration = 465 - 10 - 45 = 410.
    opt.add(tj_end <= 410)
    
    # Also, Jason's meeting must end within his available window.
    opt.add(tj_end <= jason_available_end)
    
    # For Kenneth's meeting, enforce his availability window and duration.
    opt.add(tk_start >= kenneth_available_start)
    opt.add(tk_end <= kenneth_available_end)
    opt.add(tk_end - tk_start >= required_kenneth_duration)
    
    # Travel constraint: after finishing the meeting with Jason at Presidio,
    # we travel to Marina District. The meeting with Kenneth can only start
    # after tj_end + travel_Presidio_to_Marina.
    opt.add(tk_start >= tj_end + travel_Presidio_to_Marina)
    
    # We now set the objective to maximize the total meeting time
    # (i.e. meeting duration with Jason plus meeting duration with Kenneth).
    total_meeting_time = (tj_end - tj_start) + (tk_end - tk_start)
    opt.maximize(total_meeting_time)
    
    # Check for a solution and build the itinerary.
    if opt.check() == sat:
        m = opt.model()
        jason_meeting_start = m[tj_start].as_long()
        jason_meeting_end = m[tj_end].as_long()
        kenneth_meeting_start = m[tk_start].as_long()
        kenneth_meeting_end = m[tk_end].as_long()
        
        itinerary = [
            {
                "action": "meet",
                "location": "Presidio",
                "person": "Jason",
                "start_time": format_time(jason_meeting_start),
                "end_time": format_time(jason_meeting_end)
            },
            {
                "action": "meet",
                "location": "Marina District",
                "person": "Kenneth",
                "start_time": format_time(kenneth_meeting_start),
                "end_time": format_time(kenneth_meeting_end)
            }
        ]
        
        output = {"itinerary": itinerary}
        print(json.dumps(output, indent=2))
    else:
        # If no valid schedule is found, output an error in JSON.
        print(json.dumps({"error": "No valid schedule found"}, indent=2))

if __name__ == "__main__":
    main()