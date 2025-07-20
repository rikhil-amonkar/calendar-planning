from z3 import *

def main():
    # Convert Barbara's availability to minutes since 9:00 AM
    available_start = 4 * 60 + 15  # 1:15 PM is 4 hours 15 minutes after 9:00 AM -> 255 minutes
    available_end = 9 * 60 + 15    # 6:15 PM is 9 hours 15 minutes after 9:00 AM -> 555 minutes

    # Define the start time variable (in minutes from 9:00 AM)
    start = Int('start')
    
    # Create solver with objective to minimize start time
    opt = Optimize()
    opt.add(start >= available_start)
    opt.add(start + 45 <= available_end)
    opt.minimize(start)
    
    if opt.check() == sat:
        model = opt.model()
        start_minutes = model[start].as_long()
        
        # Convert start_minutes to HH:MM format
        total_minutes = start_minutes
        hours = 9 + total_minutes // 60
        minutes = total_minutes % 60
        start_time = f"{hours:02d}:{minutes:02d}"
        
        # Calculate end time
        end_minutes = start_minutes + 45
        end_hours = 9 + end_minutes // 60
        end_minutes_remainder = end_minutes % 60
        end_time = f"{end_hours:02d}:{end_minutes_remainder:02d}"
        
        # Create itinerary
        itinerary = [
            {
                "action": "meet",
                "person": "Barbara",
                "start_time": start_time,
                "end_time": end_time
            }
        ]
        
        # Output as JSON-formatted dictionary
        print({"itinerary": itinerary})
    else:
        print({"itinerary": []})

if __name__ == "__main__":
    main()