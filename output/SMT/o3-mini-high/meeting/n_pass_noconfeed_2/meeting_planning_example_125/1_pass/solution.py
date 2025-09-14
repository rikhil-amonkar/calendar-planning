from z3 import *
import json

def minutes_to_time_str(minutes):
    hour = minutes // 60
    minute = minutes % 60
    return f"{hour}:{minute:02d}"

def main():
    # Create an Optimize object for optimization.
    opt = Optimize()

    # Define variables for meeting times (in minutes after midnight)
    s_start = Int("s_start")  # Stephanie meeting start time at Financial District
    s_end = Int("s_end")      # Stephanie meeting end time at Financial District
    j_start = Int("j_start")  # John meeting start time at Alamo Square
    j_end = Int("j_end")      # John meeting end time at Alamo Square

    # Constants based on the problem description
    # Arrival and travel times
    arrival_time = 9 * 60         # 9:00 AM -> 540 minutes
    travel_E_to_F = 5             # Embarcadero to Financial District: 5 minutes
    travel_F_to_A = 17            # Financial District to Alamo Square: 17 minutes

    # Friends' availabilities (in minutes after midnight)
    stephanie_avail_start = 8 * 60 + 15  # Stephanie available from 8:15 AM -> 495 minutes
    stephanie_avail_end = 11 * 60 + 30     # Stephanie available until 11:30 AM -> 690 minutes
    john_avail_start = 10 * 60 + 15        # John available from 10:15 AM -> 615 minutes
    john_avail_end = 20 * 60 + 45          # John available until 8:45 PM -> 1245 minutes

    # Minimum meeting durations
    min_duration_stephanie = 90  # minutes
    min_duration_john = 30       # minutes

    # Constraints for meeting with Stephanie at the Financial District:
    # You arrive at Embarcadero at 9:00 and need 5 minutes to travel to the FD.
    opt.add(s_start >= arrival_time + travel_E_to_F)
    # Meeting must also respect her availability window.
    opt.add(s_start >= stephanie_avail_start)
    opt.add(s_end <= stephanie_avail_end)
    # Minimum meeting duration for Stephanie.
    opt.add(s_end - s_start >= min_duration_stephanie)

    # Constraints for meeting with John at Alamo Square:
    # After finishing with Stephanie, travel from FD to Alamo Square takes 17 minutes.
    opt.add(j_start >= s_end + travel_F_to_A)
    # John's meeting must start after he becomes available.
    opt.add(j_start >= john_avail_start)
    # John's meeting must finish before his availability ends.
    opt.add(j_end <= john_avail_end)
    # Minimum meeting duration for John.
    opt.add(j_end - j_start >= min_duration_john)

    # Objective: minimize the end time of John's meeting to finish the day as early as possible.
    opt.minimize(j_end)

    # Check for feasibility and extract the model.
    if opt.check() == sat:
        model = opt.model()
        s_start_val = model[s_start].as_long()
        s_end_val = model[s_end].as_long()
        j_start_val = model[j_start].as_long()
        j_end_val = model[j_end].as_long()

        itinerary = [
            {
                "action": "meet",
                "location": "Financial District",
                "person": "Stephanie",
                "start_time": minutes_to_time_str(s_start_val),
                "end_time": minutes_to_time_str(s_end_val)
            },
            {
                "action": "meet",
                "location": "Alamo Square",
                "person": "John",
                "start_time": minutes_to_time_str(j_start_val),
                "end_time": minutes_to_time_str(j_end_val)
            }
        ]
        result = {"itinerary": itinerary}
        print(json.dumps(result))
    else:
        print(json.dumps({"error": "No feasible schedule found"}))

if __name__ == "__main__":
    main()