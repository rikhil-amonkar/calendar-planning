from datetime import datetime

# Assuming constraint is a dictionary with'start' key
constraint = {"start": "1500"}  # example constraint

# Convert the start time to a datetime object
start_time = datetime.strptime(constraint["start"], "%H%M")

# Get the time component from the datetime object
end_location = start_time.time()

print(end_location)