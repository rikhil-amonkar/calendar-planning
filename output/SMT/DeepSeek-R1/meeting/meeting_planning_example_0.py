from z3 import *

def min_to_time(m):
    hours = 9 + m // 60
    mins = m % 60
    am_pm = "AM" if hours < 12 else "PM"
    if hours > 12:
        hours -= 12
    return f"{hours}:{mins:02d} {am_pm}"

s = Optimize()

# Time variables (minutes after 9:00 AM)
t1 = Int('t1')  # Depart Marina for Mission
t2 = Int('t2')  # Depart Mission for Marina

# Basic constraints
s.add(t1 >= 0)
s.add(t2 >= t1 + 20)  # Travel time to Mission

# Calculate overlap with Stephanie's availability (10:30AM-1:30PM = 90-270 mins)
arrive_mission = t1 + 20
actual_start = If(arrive_mission > 90, arrive_mission, 90)
actual_end = If(t2 < 270, t2, 270)
overlap_duration = actual_end - actual_start

# Must meet for at least 120 minutes
s.add(overlap_duration >= 120)

# Maximize time with Stephanie
s.maximize(overlap_duration)

if s.check() == sat:
    m = s.model()
    t1_val = m[t1].as_long()
    t2_val = m[t2].as_long()
    
    # Calculate derived times
    arrive_mission_time = t1_val + 20
    depart_mission_time = t2_val
    mission_start = max(arrive_mission_time, 90)
    mission_end = min(depart_mission_time, 270)
    duration = mission_end - mission_start
    
    # Build schedule
    schedule = []
    schedule.append(f"{min_to_time(0)} - {min_to_time(t1_val)}: Marina District")
    schedule.append(f"{min_to_time(t1_val)} - {min_to_time(arrive_mission_time)}: Travel to Mission (20 mins)")
    schedule.append(f"{min_to_time(mission_start)} - {min_to_time(mission_end)}: Meet Stephanie ({duration} mins)")
    
    # Add return trip if applicable
    if depart_mission_time <= 270:
        return_arrival = depart_mission_time + 19
        schedule.append(f"{min_to_time(depart_mission_time)} - {min_to_time(return_arrival)}: Return to Marina (19 mins)")
    
    print("SOLUTION:")
    print("\n".join(schedule))
else:
    print("No valid schedule found")