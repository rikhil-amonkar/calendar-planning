# Add constraints for meeting Steven
s.add(And(times[9] >= start_time + 11 * 60,  # 11:15 AM
          times[9] <= start_time + 21 * 60,  # 9:15 PM
          times[0] >= times[9],  # Meeting at Alamo Square
          times[0] + 105 >= times[9]))  # Meeting for at least 105 minutes