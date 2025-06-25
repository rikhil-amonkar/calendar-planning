# Add constraints for visiting exactly 3 locations
location_counts = [x_ggp_ams, x_ggp_prd, x_ggp_rsh, x_ams_ggp, x_ams_prd, x_ams_rsh, x_prd_ggp, x_prd_ams, x_prd_rsh, x_rsh_ggp, x_rsh_ams, x_rsh_prd]
for i in range(len(location_counts)):
    for j in range(i+1, len(location_counts)):
        solver.add(location_counts[i] + location_counts[j] <= 1)