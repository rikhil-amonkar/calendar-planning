import z3

solver = z3.Optimize()
day = z3.Int('day')
S = z3.Int('S')

# Day constraints: 0=Monday, 1=Tuesday, 2=Wednesday
solver.add(day >= 0, day <= 2)
# Time constraints within the chosen day (minutes since 9:00)
solver.add(S >= 420)  # Must start at or after 16:00 (420 minutes)
solver.add(S + 30 <= 480)  # Meeting ends by 17:00

# Amy's constraints (only busy on Wednesday)
solver.add(z3.Implies(day == 2, z3.And(
    z3.Or(S + 30 <= 120, S >= 150),  # Avoid 11:00-11:30 (120-150)
    z3.Or(S + 30 <= 270, S >= 300)   # Avoid 13:30-14:00 (270-300)
)))

# Pamela's constraints for each day (blocked times converted to minutes)
solver.add(z3.Implies(day == 0, z3.And(  # Monday
    z3.Or(S + 30 <= 90, S >= 120),       # Avoid 9:00-10:30 & 11:00-16:30
    S >= 450                              # Only available 16:30-17:00
)))
solver.add(z3.Implies(day == 1, z3.Or())) # Tuesday has no valid slots
solver.add(z3.Implies(day == 2, z3.And(  # Wednesday
    z3.Or(S + 30 <= 30, (S >= 60) & (S + 30 <= 120), S >= 150),  # Avoid morning blocks
    z3.Or(S + 30 <= 330, S >= 360),      # Avoid 14:30-15:00 (330-360)
    z3.Or(S >= 450)                      # Only available 16:30-17:00
)))

# Find earliest possible day and time
solver.minimize(day * 1000 + S)

if solver.check() == z3.sat:
    model = solver.model()
    d = model[day].as_long()
    s = model[S].as_long()
    days = ["Monday", "Tuesday", "Wednesday"]
    start_h = 9 + s // 60
    start_m = s % 60
    end_h = 9 + (s + 30) // 60
    end_m = (s + 30) % 60
    print(f"{days[d]}\n{start_h}:{start_m:02d}\n{end_h}:{end_m:02d}")
else:
    print("No solution found")