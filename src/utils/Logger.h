/**
 * @file Logger.h
 * @brief Logging utility for elomig
 *
 * Provides centralized logging functionality with multiple log levels,
 * timestamp support, and configurable output destinations.
 */

#ifndef ELOMIG_LOGGER_H
#define ELOMIG_LOGGER_H

#include <ctime>
#include <fstream>
#include <mutex>
#include <string>

namespace elomig {

/**
 * @brief Log severity levels
 */
enum class LogLevel {
	DEBUG   = 1, ///< Detailed debugging information
	INFO    = 2, ///< General information
	STATUS  = 3, ///< Progress/status messages
	WARNING = 4, ///< Warning conditions
	ERROR   = 5  ///< Error conditions
};

/**
 * @brief Logger singleton class
 *
 * Thread-safe logging utility that supports multiple log levels,
 * file output, and console output with configurable formatting.
 *
 * This class provides centralized logging for the elomig toolchain, supporting
 * different verbosity levels and configurable output destinations.
 * It is designed to be used throughout the application with convenience macros
 * like LOG_DEBUG(), LOG_INFO(), etc.
 *
 * @ingroup Utilities
 */
class Logger {
public:
	/**
	 * @brief Get the singleton instance
	 *
	 * Returns the single Logger instance for the application. This method
	 * is thread-safe and can be called from any thread.
	 *
	 * @return Reference to the singleton Logger instance
	 * @retval Logger& The global logger instance
	 *
	 * @note This function creates the logger instance on first call if it doesn't exist
	 *
	 * @see initialize()
	 */
	static Logger& getInstance();

	/**
	 * @brief Initialize the logger
	 *
	 * Configures the logger with output destination and minimum log level.
	 * Can be called multiple times to reconfigure the logger.
	 *
	 * @param logFile Path to the log file (empty for console only)
	 * @param minLevel Minimum log level to output (default: STATUS)
	 * @param showDebug Enable debug output (default: false)
	 *
	 * @retval void
	 *
	 * @note If logFile is empty, all output goes to stderr
	 * @note Setting showDebug=true enables DEBUG level output
	 *
	 * @see setLogLevel()
	 * @see setDebugMode()
	 */
	void initialize( std::string const& logFile, LogLevel minLevel = LogLevel::STATUS, bool showDebug = false );

	/**
	 * @brief Set the minimum log level
	 *
	 * Configures the minimum severity level that will be logged.
	 * Messages with lower severity will be filtered out.
	 *
	 * @param level Minimum level to output
	 *
	 * @retval void
	 *
	 * @note This affects all future log messages
	 *
	 * @see getLogLevel()
	 * @see setDebugMode()
	 */
	void setLogLevel( LogLevel level );

	/**
	 * @brief Enable or disable debug mode
	 *
	 * When enabled, debug messages are logged in addition to other levels.
	 * This is equivalent to calling setLogLevel(LogLevel::DEBUG) but more convenient.
	 *
	 * @param enabled True to enable debug output
	 *
	 * @retval void
	 *
	 * @note This is a convenience method that calls setLogLevel() internally
	 *
	 * @see setLogLevel()
	 * @see isDebugMode()
	 */
	void setDebugMode( bool enabled );

	/**
	 * @brief Log a debug message
	 *
	 * Logs a message at DEBUG level. Debug messages are typically used for
	 * detailed information helpful for troubleshooting and development.
	 *
	 * @param format Printf-style format string
	 * @param ... Format arguments
	 *
	 * @retval void
	 *
	 * @note Debug messages are only logged when debug mode is enabled
	 * @note Uses variadic arguments for formatted output
	 *
	 * @see LOG_DEBUG() convenience macro
	 * @see setDebugMode()
	 * @see debug()
	 */
	void debug( char const* format, ... ) __attribute__(( format( printf, 2, 3 ) ));

	/**
	 * @brief Log an info message
	 *
	 * Logs a message at INFO level. Info messages provide general information
	 * about the application's operation and progress.
	 *
	 * @param format Printf-style format string
	 * @param ... Format arguments
	 *
	 * @retval void
	 *
	 * @note This is the default logging level for most operational messages
	 * @note Uses variadic arguments for formatted output
	 *
	 * @see LOG_INFO() convenience macro
	 * @see info()
	 */
	void info( char const* format, ... ) __attribute__(( format( printf, 2, 3 ) ));

	/**
	 * @brief Log a status message
	 *
	 * Logs a message at STATUS level. Status messages indicate progress
	 * in long-running operations or significant events in the application flow.
	 *
	 * @param format Printf-style format string
	 * @param ... Format arguments
	 *
	 * @retval void
	 *
	 * @note This is the default minimum logging level for the application
	 * @note Uses variadic arguments for formatted output
	 *
	 * @see LOG_STATUS() convenience macro
	 * @see status()
	 */
	void status( char const* format, ... ) __attribute__(( format( printf, 2, 3 ) ));

	/**
	 * @brief Log a warning message
	 *
	 * Logs a message at WARNING level. Warnings indicate potential issues
	 * that don't stop execution but should be investigated.
	 *
	 * @param format Printf-style format string
	 * @param ... Format arguments
	 *
	 * @retval void
	 *
	 * @note Uses variadic arguments for formatted output
	 *
	 * @see LOG_WARNING() convenience macro
	 * @see warning()
	 */
	void warning( char const* format, ... ) __attribute__(( format( printf, 2, 3 ) ));

	/**
	 * @brief Log an error message
	 *
	 * Logs a message at ERROR level. Errors indicate problems that
	 * prevent normal operation or completion of a task.
	 *
	 * @param format Printf-style format string
	 * @param ... Format arguments
	 *
	 * @retval void
	 *
	 * @note Uses variadic arguments for formatted output
	 *
	 * @see LOG_ERROR() convenience macro
	 * @see error()
	 */
	void error( char const* format, ... ) __attribute__(( format( printf, 2, 3 ) ));

	/**
	 * @brief Log a status message with progress indicator
	 *
	 * Logs a message at STATUS level with special handling for progress updates.
	 * Progress messages are typically used for long-running operations to show
	 * the user the current state of processing.
	 *
	 * @param isProgress True if this is a progress update
	 * @param format Printf-style format string
	 * @param ... Format arguments
	 *
	 * @retval void
	 *
	 * @note Progress updates may be displayed differently to distinguish them
	 * @note Uses variadic arguments for formatted output
	 *
	 * @see LOG_STATUS() convenience macro
	 * @see progress()
	 */
	void progress( bool isProgress, char const* format, ... ) __attribute__(( format( printf, 3, 4 ) ));

	/**
	 * @brief Get current timestamp string
	 * @return Timestamp in YYYY-MM-DD HH:MM:SS format
	 */
	std::string getTimestamp() const;

	/**
	 * @brief Check if debug mode is enabled
	 * @return True if debug output is enabled
	 */
	bool isDebugMode() const { return m_debugMode; }

	/**
	 * @brief Get the current log level
	 * @return Current minimum log level
	 */
	LogLevel getLogLevel() const { return m_minLevel; }

	/**
	 * @brief Set global error return flag
	 * @param value Error flag value (typically 1)
	 */
	void setGlobalError( int value ) { m_globalError = value; }

	/**
	 * @brief Get the global error return flag
	 * @return Error flag value
	 */
	int getGlobalError() const { return m_globalError; }

private:
	Logger() = default;
	~Logger();

	// Delete copy constructor and assignment operator
	Logger( Logger const& )             = delete;
	Logger& operator= ( Logger const& ) = delete;

	/**
	 * @brief Internal logging method
	 * @param level Log level
	 * @param format Format string
	 * @param args Format arguments
	 */
	void log( LogLevel level, char const* format, va_list args );

	/**
	 * @brief Format and output a log message
	 * @param level Log level
	 * @param message Formatted message
	 */
	void                     output( LogLevel level, std::string const& message );

	std::ofstream            m_logFile;     ///< Log file stream
	std::string              m_logFilePath; ///< Path to log file
	LogLevel                 m_minLevel;    ///< Minimum log level
	bool                     m_debugMode;   ///< Debug mode flag
	bool                     m_initialized; ///< Initialization flag
	mutable std::mutex       m_mutex;       ///< Thread safety mutex
	int                      m_globalError; ///< Global error flag

	static std::string const LEVEL_NAMES[]; ///< Log level names
};

// Convenience macros
#define LOG_DEBUG( ... )   elomig::Logger::getInstance().debug( __VA_ARGS__ )
#define LOG_INFO( ... )    elomig::Logger::getInstance().info( __VA_ARGS__ )
#define LOG_STATUS( ... )  elomig::Logger::getInstance().status( __VA_ARGS__ )
#define LOG_WARNING( ... ) elomig::Logger::getInstance().warning( __VA_ARGS__ )
#define LOG_ERROR( ... )   elomig::Logger::getInstance().error( __VA_ARGS__ )

} // namespace elomig

#endif // ELOMIG_LOGGER_H
