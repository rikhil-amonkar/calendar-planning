from z3 import Optimize, Int, sat
import json

def main():
    opt = Optimize()

    # Define meeting start times and durations (in minutes since midnight) for each friend.
    H_start = Int('H_start')  # Helen meeting start time (North Beach)
    H_dur = Int('H_dur')      # Helen meeting duration
    
    K_start = Int('K_start')  # Kimberly meeting start time (Fisherman's Wharf)
    K_dur = Int('K_dur')      # Kimberly meeting duration
    
    P_start = Int('P_start')  # Patricia meeting start time (Bayview)
    P_dur = Int('P_dur')      # Patricia meeting duration

    # Calculate meeting end times
    H_end = H_start + H_dur
    K_end = K_start + K_dur
    P_end = P_start + P_dur

    # Minimum meeting durations (in minutes)
    opt.add(H_dur >= 120)
    opt.add(K_dur >= 45)
    opt.add(P_dur >= 120)

    # Time conversion: minutes since midnight
    # Arrival at Nob Hill: 9:00 is 9*60 = 540. 
    # Travel from Nob Hill to North Beach (Helen) takes 8 minutes.
    opt.add(H_start >= 540 + 8)  # Must start at or after 9:08 (548)

    # Helen is available at North Beach from 7:00 (420) to 16:45 (1005)
    opt.add(H_start >= 420)
    opt.add(H_end <= 1005)

    # Kimberly is available at Fisherman's Wharf from 16:30 (990) to 21:00 (1260)
    opt.add(K_start >= 990)
    opt.add(K_end <= 1260)

    # Patricia is available at Bayview from 18:00 (1080) to 21:15 (1275)
    opt.add(P_start >= 1080)
    opt.add(P_end <= 1275)

    # Travel time constraints between meetings:
    # From North Beach (Helen) to Fisherman's Wharf (Kimberly) takes 5 minutes.
    opt.add(K_start >= H_end + 5)
    
    # From Fisherman's Wharf (Kimberly) to Bayview (Patricia) takes 26 minutes.
    opt.add(P_start >= K_end + 26)

    # We want to minimize idle waiting time.
    # Idle time components:
    idle1 = H_start - (540 + 8)        # Waiting after arriving at Nob Hill and traveling to North Beach.
    idle2 = K_start - (H_end + 5)        # Waiting between finishing Helen meeting and starting Kimberly meeting.
    idle3 = P_start - (K_end + 26)       # Waiting between finishing Kimberly meeting and starting Patricia meeting.
    total_idle = idle1 + idle2 + idle3

    opt.minimize(total_idle)

    if opt.check() == sat:
        model = opt.model()
        Hs = model[H_start].as_long()
        Hd = model[H_dur].as_long()
        He = Hs + Hd
        
        Ks = model[K_start].as_long()
        Kd = model[K_dur].as_long()
        Ke = Ks + Kd
        
        Ps = model[P_start].as_long()
        Pd = model[P_dur].as_long()
        Pe = Ps + Pd

        # Function to convert minutes since midnight to H:MM 24-hour format.
        def to_time(total_minutes):
            hours = total_minutes // 60
            minutes = total_minutes % 60
            return f"{hours}:{minutes:02d}"

        itinerary = [
            {
                "action": "meet",
                "location": "North Beach",
                "person": "Helen",
                "start_time": to_time(Hs),
                "end_time": to_time(He)
            },
            {
                "action": "meet",
                "location": "Fisherman's Wharf",
                "person": "Kimberly",
                "start_time": to_time(Ks),
                "end_time": to_time(Ke)
            },
            {
                "action": "meet",
                "location": "Bayview",
                "person": "Patricia",
                "start_time": to_time(Ps),
                "end_time": to_time(Pe)
            }
        ]
        
        result = { "itinerary": itinerary }
        print(json.dumps(result))
    else:
        print(json.dumps({"itinerary": []}))

if __name__ == '__main__':
    main()