import json
from z3 import Int, Solver, sat

def minutes_to_time(m):
    """Convert minutes since midnight to a string in H:MM 24-hour format."""
    h = m // 60
    r = m % 60
    return f"{h}:{r:02d}"

def main():
    # We model the day in minutes since midnight.
    # 9:00 AM  -> 9 * 60 = 540 minutes
    # 19:00   -> 19 * 60 = 1140 minutes
    # 20:15   -> 20 * 60 + 15 = 1215 minutes
    # Travel times:
    #   Russian Hill -> Richmond District: 14 minutes
    
    # Decision variables:
    # Meeting with our "local friend" at Russian Hill.
    alice_start = Int('alice_start')      # Start time (must be 9:00)
    alice_end   = Int('alice_end')        # End time (when we depart from Russian Hill)
    
    # Our departure time from Russian Hill. (This will be set by the constraints.)
    departure = Int('departure')
    
    # Meeting with Daniel (at Richmond District).
    daniel_start = Int('daniel_start')    # Time we start meeting Daniel
    daniel_end   = Int('daniel_end')      # End time of meeting Daniel
    meeting_duration = Int('meeting_duration')  # Duration of meeting with Daniel
    
    # Create the SMT solver and add constraints.
    s = Solver()

    # We arrive at Russian Hill at 9:00.
    s.add(alice_start == 9 * 60)  # 540 minutes
    # We can meet our local friend (Alice) from arrival until we leave.
    s.add(alice_end == departure)
    s.add(departure >= alice_start)

    # To meet Daniel, we must travel from Russian Hill to Richmond District.
    # Travel time is 14 minutes.
    s.add(daniel_start == departure + 14)
    
    # Daniel is at Richmond District from 19:00 (1140 minutes) to 20:15 (1215 minutes).
    s.add(daniel_start >= 19 * 60)           # Must arrive no earlier than 19:00
    s.add(daniel_end <= 20 * 60 + 15)          # Meeting must end by 20:15

    # Daniel meeting must last at least 75 minutes.
    s.add(meeting_duration >= 75)
    s.add(daniel_end == daniel_start + meeting_duration)
    
    # Ensure that the meeting with Daniel fits inside his available window.
    s.add(meeting_duration <= (20 * 60 + 15) - (departure + 14))
    
    # The constraints force a unique departure time:
    # To start Daniel's meeting no earlier than 19:00 we need: departure + 14 >= 1140  => departure >= 1126.
    # And to get a full 75-minute meeting, we need: meeting_duration <= 1215 - (departure+14)
    #   i.e. 75 <= 1215 - (departure+14)  => departure <= 1126.
    # So departure must be exactly 1126 (i.e. 18:46).
    s.add(departure == 1126)

    # Solve the constraints.
    if s.check() == sat:
        m = s.model()
        alice_start_val = m[alice_start].as_long()
        alice_end_val   = m[alice_end].as_long()
        daniel_start_val = m[daniel_start].as_long()
        daniel_end_val   = m[daniel_end].as_long()
        
        # Build the itinerary.
        # We'll assume that while waiting at Russian Hill you meet a friend named Alice,
        # and then you travel and meet Daniel at Richmond District.
        itinerary = [
            {
                "action": "meet",
                "location": "Russian Hill",
                "person": "Alice",
                "start_time": minutes_to_time(alice_start_val),
                "end_time": minutes_to_time(alice_end_val)
            },
            {
                "action": "meet",
                "location": "Richmond District",
                "person": "Daniel",
                "start_time": minutes_to_time(daniel_start_val),
                "end_time": minutes_to_time(daniel_end_val)
            }
        ]
        
        result = {"itinerary": itinerary}
        print(json.dumps(result, indent=2))
    else:
        print(json.dumps({"error": "No valid meeting schedule found."}))

if __name__ == "__main__":
    main()