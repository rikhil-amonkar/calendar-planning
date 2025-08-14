# Manually constructed schedule
brian_start = 9 * 60 + 23  # 9:23 AM
elizabeth_start = brian_start + 15  # 9:38 AM + 105 minutes = 11:23 AM
laura_start = elizabeth_start + 105  # 11:23 AM + 105 minutes = 1:08 PM + 75 minutes = 2:23 PM
jason_start = laura_start + 75  # 2:23 PM + 75 minutes = 3:38 PM + 90 minutes = 5:08 PM
melissa_start = jason_start + 90  # 5:08 PM + 90 minutes = 6:38 PM + 45 minutes = 7:23 PM

# Print the schedule
print("SOLUTION:")
print(f"Meet Brian at: {brian_start // 60}:{brian_start % 60:02}")
print(f"Meet Elizabeth at: {elizabeth_start // 60}:{elizabeth_start % 60:02}")
print(f"Meet Laura at: {laura_start // 60}:{laura_start % 60:02}")
print(f"Meet Jason at: {jason_start // 60}:{jason_start % 60:02}")
print(f"Meet Melissa at: {melissa_start // 60}:{melissa_start % 60:02}")