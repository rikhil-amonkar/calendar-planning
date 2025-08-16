from z3 import Optimize, Int, If
import json

# Helper to convert minutes-since-midnight to "HH:MM" format
def minutes_to_time(m):
    hours = m // 60
    minutes = m % 60
    return f"{hours:02d}:{minutes:02d}"

# Create an optimizer instance.
opt = Optimize()

# We use minutes past midnight as our time unit.
# Some key times:
#  9:00 AM = 9*60 = 540
#  7:45 AM = 465, 8:30 AM = 510, 10:30 AM = 630
#  14:45 = 14*60+45 = 885, 17:00 = 1020,
#  19:15 = 1155, 19:45 = 1185, 20:00 = 1200, 20:45 = 1245, 21:45 = 1305

# Decision variables: meeting start and end times (in minutes) for the friends we can schedule.
# Note: We omit Robert because his availability (7:45-10:30 for a 90-minute meeting) is impossible
# given our mandatory arrival at Haight-Ashbury at 9:00.
anthony_start = Int("anthony_start")
anthony_end   = Int("anthony_end")
steven_start  = Int("steven_start")
steven_end    = Int("steven_end")
sandra_start  = Int("sandra_start")
sandra_end    = Int("sandra_end")
stephanie_start = Int("stephanie_start")
stephanie_end   = Int("stephanie_end")
kevin_start     = Int("kevin_start")
kevin_end       = Int("kevin_end")

# Constraints for Anthony (meeting at Alamo Square):
# - Travel: from initial Haight-Ashbury (arriving at 9:00 = 540) to Alamo Square takes 5 minutes.
# - Availability: 7:45 (465) to 19:45 (1185)
# - Minimum meeting duration: 15 minutes.
opt.add(anthony_start >= 540 + 5)  # must leave Haight-Ashbury at 9:00 plus 5 minutes travel
opt.add(anthony_end == anthony_start + 15)
opt.add(anthony_start >= 465)
opt.add(anthony_end <= 1185)

# Constraints for Steven (meeting at Golden Gate Park):
# - Travel: from Alamo Square to Golden Gate Park takes 9 minutes.
# - Availability: 8:30 (510) to 17:00 (1020)
# - Minimum meeting duration: 75 minutes.
opt.add(steven_start >= anthony_end + 9)
opt.add(steven_start >= 510)
opt.add(steven_end == steven_start + 75)
opt.add(steven_end <= 1020)

# Constraints for Sandra (meeting at Pacific Heights):
# - Travel: from Golden Gate Park to Pacific Heights takes 16 minutes.
# - Availability: 14:45 (885) to 21:45 (1305)
# - Minimum meeting duration: 45 minutes.
opt.add(sandra_start >= If(steven_end + 16 > 885, steven_end + 16, 885))
opt.add(sandra_end == sandra_start + 45)
opt.add(sandra_end <= 1305)

# Constraints for Stephanie (meeting at Russian Hill):
# - Travel: from Pacific Heights to Russian Hill takes 7 minutes.
# - Availability: 20:00 (1200) to 20:45 (1245)
# - Minimum meeting duration: 15 minutes.
opt.add(stephanie_start >= If(sandra_end + 7 > 1200, sandra_end + 7, 1200))
opt.add(stephanie_end == stephanie_start + 15)
opt.add(stephanie_end <= 1245)

# Constraints for Kevin (meeting at Fisherman's Wharf):
# - Travel: from Russian Hill to Fisherman's Wharf takes 7 minutes.
# - Availability: 19:15 (1155) to 21:45 (1305)
# - Minimum meeting duration: 75 minutes.
opt.add(kevin_start >= If(stephanie_end + 7 > 1155, stephanie_end + 7, 1155))
opt.add(kevin_end == kevin_start + 75)
opt.add(kevin_end <= 1305)

# To “optimize” our schedule we can minimize the final finishing time.
opt.minimize(kevin_end)

if opt.check() == sat:
    model = opt.model()
    itinerary = []
    # Build the itinerary in order.
    itinerary.append({
        "action": "meet",
        "person": "Anthony",
        "start_time": minutes_to_time(model[anthony_start].as_long()),
        "end_time": minutes_to_time(model[anthony_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Steven",
        "start_time": minutes_to_time(model[steven_start].as_long()),
        "end_time": minutes_to_time(model[steven_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Sandra",
        "start_time": minutes_to_time(model[sandra_start].as_long()),
        "end_time": minutes_to_time(model[sandra_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Stephanie",
        "start_time": minutes_to_time(model[stephanie_start].as_long()),
        "end_time": minutes_to_time(model[stephanie_end].as_long())
    })
    itinerary.append({
        "action": "meet",
        "person": "Kevin",
        "start_time": minutes_to_time(model[kevin_start].as_long()),
        "end_time": minutes_to_time(model[kevin_end].as_long())
    })
    
    output = {"itinerary": itinerary}
    print(json.dumps(output, indent=2))
else:
    print("No solution found.")