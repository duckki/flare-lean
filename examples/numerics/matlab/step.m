function [next_mean, next_variance] = step(mean, variance, measurement, ...
                                         process_noise, measurement_noise)
% Inputs are original real double scalars, not matrices or single precision.
variance = variance + process_noise;
gain = variance ./ (variance + measurement_noise);
next_mean = mean + gain .* (measurement - mean);
next_variance = (1 - gain) .* variance;
end
